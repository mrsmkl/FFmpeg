/*
 * Copyright (c) 2007-2010 Stefano Sabatini
 *
 * This file is part of FFmpeg.
 *
 * FFmpeg is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * FFmpeg is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with FFmpeg; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

/**
 * @file
 * simple media prober based on the FFmpeg libraries
 */

#include "config.h"
#include "libavutil/ffversion.h"

#include <string.h>

#include "libavformat/avformat.h"
#include "libavcodec/avcodec.h"
#include "libavutil/avassert.h"
#include "libavutil/avstring.h"
#include "libavutil/bprint.h"
#include "libavutil/display.h"
#include "libavutil/hash.h"
#include "libavutil/mastering_display_metadata.h"
#include "libavutil/opt.h"
#include "libavutil/pixdesc.h"
#include "libavutil/spherical.h"
#include "libavutil/stereo3d.h"
#include "libavutil/dict.h"
#include "libavutil/intreadwrite.h"
#include "libavutil/libm.h"
#include "libavutil/parseutils.h"
#include "libavutil/timecode.h"
#include "libavutil/timestamp.h"
#include "libavdevice/avdevice.h"
#include "libswscale/swscale.h"
#include "libswresample/swresample.h"
#include "libpostproc/postprocess.h"
#include "cmdutils.h"

#include "libavutil/thread.h"

#if !HAVE_THREADS
#  ifdef pthread_mutex_lock
#    undef pthread_mutex_lock
#  endif
#  define pthread_mutex_lock(a) do{}while(0)
#  ifdef pthread_mutex_unlock
#    undef pthread_mutex_unlock
#  endif
#  define pthread_mutex_unlock(a) do{}while(0)
#endif

typedef struct InputStream {
    AVStream *st;

    AVCodecContext *dec_ctx;
} InputStream;

typedef struct InputFile {
    AVFormatContext *fmt_ctx;

    InputStream *streams;
    int       nb_streams;
} InputFile;

const char program_name[] = "ffprobe";
const int program_birth_year = 2007;

static int do_show_log = 0;

typedef struct ReadInterval {
    int id;             ///< identifier
    int64_t start, end; ///< start, end in second/AV_TIME_BASE units
    int has_start, has_end;
    int start_is_offset, end_is_offset;
    int duration_frames;
} ReadInterval;

static ReadInterval *read_intervals;
static int read_intervals_nb = 0;

static int find_stream_info  = 1;

/* section structure definition */


/* FFprobe context */
static AVInputFormat *iformat = NULL;

static const struct {
    double bin_val;
    double dec_val;
    const char *bin_str;
    const char *dec_str;
} si_prefixes[] = {
    { 1.0, 1.0, "", "" },
    { 1.024e3, 1e3, "Ki", "K" },
    { 1.048576e6, 1e6, "Mi", "M" },
    { 1.073741824e9, 1e9, "Gi", "G" },
    { 1.099511627776e12, 1e12, "Ti", "T" },
    { 1.125899906842624e15, 1e15, "Pi", "P" },
};

static const char unit_second_str[]         = "s"    ;
static const char unit_hertz_str[]          = "Hz"   ;
static const char unit_byte_str[]           = "byte" ;
static const char unit_bit_per_second_str[] = "bit/s";

static int nb_streams;
static uint64_t *nb_streams_packets;
static uint64_t *nb_streams_frames;
static int *selected_streams;

#if HAVE_THREADS
pthread_mutex_t log_mutex;
#endif
typedef struct LogBuffer {
    char *context_name;
    int log_level;
    char *log_message;
    AVClassCategory category;
    char *parent_name;
    AVClassCategory parent_category;
}LogBuffer;

struct unit_value {
    union { double d; long long int i; } val;
    const char *unit;
};


#define REALLOCZ_ARRAY_STREAM(ptr, cur_n, new_n)                        \
{                                                                       \
    ret = av_reallocp_array(&(ptr), (new_n), sizeof(*(ptr)));           \
    if (ret < 0)                                                        \
        goto end;                                                       \
    memset( (ptr) + (cur_n), 0, ((new_n) - (cur_n)) * sizeof(*(ptr)) ); \
}


static void log_read_interval(const ReadInterval *interval, void *log_ctx, int log_level)
{
    av_log(log_ctx, log_level, "id:%d", interval->id);

    if (interval->has_start) {
        av_log(log_ctx, log_level, " start:%s%s", interval->start_is_offset ? "+" : "",
               av_ts2timestr(interval->start, &AV_TIME_BASE_Q));
    } else {
        av_log(log_ctx, log_level, " start:N/A");
    }

    if (interval->has_end) {
        av_log(log_ctx, log_level, " end:%s", interval->end_is_offset ? "+" : "");
        if (interval->duration_frames)
            av_log(log_ctx, log_level, "#%"PRId64, interval->end);
        else
            av_log(log_ctx, log_level, "%s", av_ts2timestr(interval->end, &AV_TIME_BASE_Q));
    } else {
        av_log(log_ctx, log_level, " end:N/A");
    }

    av_log(log_ctx, log_level, "\n");
}

static int read_interval_packet_sizes(InputFile *ifile,
                                 const ReadInterval *interval, int64_t *cur_ts)
{
    AVFormatContext *fmt_ctx = ifile->fmt_ctx;
    AVPacket pkt;
    AVFrame *frame = NULL;
    int ret = 0, i = 0, frame_count = 0;
    int total_size = 0;
    int64_t start = -INT64_MAX, end = interval->end;
    int has_start = 0, has_end = interval->has_end && !interval->end_is_offset;

    av_init_packet(&pkt);

    av_log(NULL, AV_LOG_VERBOSE, "Processing read interval ");
    log_read_interval(interval, NULL, AV_LOG_VERBOSE);

    if (interval->has_start) {
        int64_t target;
        if (interval->start_is_offset) {
            if (*cur_ts == AV_NOPTS_VALUE) {
                av_log(NULL, AV_LOG_ERROR,
                       "Could not seek to relative position since current "
                       "timestamp is not defined\n");
                ret = AVERROR(EINVAL);
                goto end;
            }
            target = *cur_ts + interval->start;
        } else {
            target = interval->start;
        }

        av_log(NULL, AV_LOG_VERBOSE, "Seeking to read interval start point %s\n",
               av_ts2timestr(target, &AV_TIME_BASE_Q));
        if ((ret = avformat_seek_file(fmt_ctx, -1, -INT64_MAX, target, INT64_MAX, 0)) < 0) {
            av_log(NULL, AV_LOG_ERROR, "Could not seek to position %"PRId64": %s\n",
                   interval->start, av_err2str(ret));
            goto end;
        }
    }

    frame = av_frame_alloc();
    if (!frame) {
        ret = AVERROR(ENOMEM);
        goto end;
    }
    while (!av_read_frame(fmt_ctx, &pkt)) {
        if (ifile->nb_streams > nb_streams) {
            REALLOCZ_ARRAY_STREAM(nb_streams_frames,  nb_streams, fmt_ctx->nb_streams);
            REALLOCZ_ARRAY_STREAM(nb_streams_packets, nb_streams, fmt_ctx->nb_streams);
            REALLOCZ_ARRAY_STREAM(selected_streams,   nb_streams, fmt_ctx->nb_streams);
            nb_streams = ifile->nb_streams;
        }
        if (selected_streams[pkt.stream_index]) {
            AVRational tb = ifile->streams[pkt.stream_index].st->time_base;

            if (pkt.pts != AV_NOPTS_VALUE)
                *cur_ts = av_rescale_q(pkt.pts, tb, AV_TIME_BASE_Q);

            if (!has_start && *cur_ts != AV_NOPTS_VALUE) {
                start = *cur_ts;
                has_start = 1;
            }

            if (has_start && !has_end && interval->end_is_offset) {
                end = start + interval->end;
                has_end = 1;
            }

            if (interval->end_is_offset && interval->duration_frames) {
                if (frame_count >= interval->end)
                    break;
            } else if (has_end && *cur_ts != AV_NOPTS_VALUE && *cur_ts >= end) {
                break;
            }

            frame_count++;
            // show_packet(w, ifile, &pkt, 
            
            total_size += pkt.size;
            fprintf(stderr, "Size %d\n", total_size);
            
            i++;
            // show_packet_size(ifile, &pkt, i++);
            nb_streams_packets[pkt.stream_index]++;
            /*
            if (do_read_frames) {
                int packet_new = 1;
                while (process_frame(w, ifile, frame, &pkt, &packet_new) > 0);
            }*/
        }
        av_packet_unref(&pkt);
    }
    av_init_packet(&pkt);
    pkt.data = NULL;
    pkt.size = 0;
    //Flush remaining frames that are cached in the decoder
    /*
    for (i = 0; i < fmt_ctx->nb_streams; i++) {
        pkt.stream_index = i;
        if (do_read_frames)
            while (process_frame(w, ifile, frame, &pkt, &(int){1}) > 0);
    }*/

end:
    av_frame_free(&frame);
    if (ret < 0) {
        av_log(NULL, AV_LOG_ERROR, "Could not read packets in interval ");
        log_read_interval(interval, NULL, AV_LOG_ERROR);
    }
    return total_size;
}


static int read_packet_sizes(InputFile *ifile)
{
    AVFormatContext *fmt_ctx = ifile->fmt_ctx;
    int i, ret = 0;
    int64_t cur_ts = fmt_ctx->start_time;
    
    int total_size = 0;

    if (read_intervals_nb == 0) {
        ReadInterval interval = (ReadInterval) { .has_start = 0, .has_end = 0 };
        ret = read_interval_packet_sizes(ifile, &interval, &cur_ts);
        total_size += ret;
    } else {
        for (i = 0; i < read_intervals_nb; i++) {
            ret = read_interval_packet_sizes(ifile, &read_intervals[i], &cur_ts);
            if (ret < 0)
                break;
            total_size += ret;
        }
    }
    
    uint8_t arr[32];
    for (i = 0; i < 32; i++) arr[i] = 0;
    for (i = 0; i < 4; i++) {
        arr[31-i] = total_size&0xff;
        total_size = total_size >> 8;
    }
    FILE *f = fopen("output.data", "wb");
    if (!f) {
        fprintf(stderr, "Cannot open file output.data for writing\n");
        exit(-1);
    }
    fwrite(arr, 1, 32, f);
    fclose(f);

    return ret;
}



static int open_input_file(InputFile *ifile, const char *filename)
{
    int err, i;
    AVFormatContext *fmt_ctx = NULL;
    AVDictionaryEntry *t;
    int scan_all_pmts_set = 0;

    fmt_ctx = avformat_alloc_context();
    if (!fmt_ctx) {
        print_error(filename, AVERROR(ENOMEM));
        exit_program(1);
    }

    if (!av_dict_get(format_opts, "scan_all_pmts", NULL, AV_DICT_MATCH_CASE)) {
        av_dict_set(&format_opts, "scan_all_pmts", "1", AV_DICT_DONT_OVERWRITE);
        scan_all_pmts_set = 1;
    }
    if ((err = avformat_open_input(&fmt_ctx, filename,
                                   iformat, &format_opts)) < 0) {
        print_error(filename, err);
        return err;
    }
    ifile->fmt_ctx = fmt_ctx;
    if (scan_all_pmts_set)
        av_dict_set(&format_opts, "scan_all_pmts", NULL, AV_DICT_MATCH_CASE);
    if ((t = av_dict_get(format_opts, "", NULL, AV_DICT_IGNORE_SUFFIX))) {
        av_log(NULL, AV_LOG_ERROR, "Option %s not found.\n", t->key);
        return AVERROR_OPTION_NOT_FOUND;
    }

    if (find_stream_info) {
        AVDictionary **opts = setup_find_stream_info_opts(fmt_ctx, codec_opts);
        int orig_nb_streams = fmt_ctx->nb_streams;

        err = avformat_find_stream_info(fmt_ctx, opts);

        for (i = 0; i < orig_nb_streams; i++)
            av_dict_free(&opts[i]);
        av_freep(&opts);

        if (err < 0) {
            print_error(filename, err);
            return err;
        }
    }

    av_dump_format(fmt_ctx, 0, filename, 0);

    ifile->streams = av_mallocz_array(fmt_ctx->nb_streams,
                                      sizeof(*ifile->streams));
    if (!ifile->streams)
        exit(1);
    ifile->nb_streams = fmt_ctx->nb_streams;

    /* bind a decoder to each input stream */
    for (i = 0; i < fmt_ctx->nb_streams; i++) {
        InputStream *ist = &ifile->streams[i];
        AVStream *stream = fmt_ctx->streams[i];
        AVCodec *codec;

        ist->st = stream;

        if (stream->codecpar->codec_id == AV_CODEC_ID_PROBE) {
            av_log(NULL, AV_LOG_WARNING,
                   "Failed to probe codec for input stream %d\n",
                    stream->index);
            continue;
        }

        codec = avcodec_find_decoder(stream->codecpar->codec_id);
        if (!codec) {
            av_log(NULL, AV_LOG_WARNING,
                    "Unsupported codec with id %d for input stream %d\n",
                    stream->codecpar->codec_id, stream->index);
            continue;
        }
        {
            AVDictionary *opts = filter_codec_opts(codec_opts, stream->codecpar->codec_id,
                                                   fmt_ctx, stream, codec);

            ist->dec_ctx = avcodec_alloc_context3(codec);
            if (!ist->dec_ctx)
                exit(1);

            err = avcodec_parameters_to_context(ist->dec_ctx, stream->codecpar);
            if (err < 0)
                exit(1);

            if (do_show_log) {
                // For loging it is needed to disable at least frame threads as otherwise
                // the log information would need to be reordered and matches up to contexts and frames
                // That is in fact possible but not trivial
                av_dict_set(&codec_opts, "threads", "1", 0);
            }

            ist->dec_ctx->pkt_timebase = stream->time_base;
            ist->dec_ctx->framerate = stream->avg_frame_rate;
#if FF_API_LAVF_AVCTX
            ist->dec_ctx->coded_width = stream->codec->coded_width;
            ist->dec_ctx->coded_height = stream->codec->coded_height;
#endif

            if (avcodec_open2(ist->dec_ctx, codec, &opts) < 0) {
                av_log(NULL, AV_LOG_WARNING, "Could not open codec for input stream %d\n",
                       stream->index);
                exit(1);
            }

            if ((t = av_dict_get(opts, "", NULL, AV_DICT_IGNORE_SUFFIX))) {
                av_log(NULL, AV_LOG_ERROR, "Option %s for input stream %d not found\n",
                       t->key, stream->index);
                return AVERROR_OPTION_NOT_FOUND;
            }
        }
    }

    ifile->fmt_ctx = fmt_ctx;
    return 0;
}

static void close_input_file(InputFile *ifile)
{
    int i;

    /* close decoder for each stream */
    for (i = 0; i < ifile->nb_streams; i++)
        if (ifile->streams[i].st->codecpar->codec_id != AV_CODEC_ID_NONE)
            avcodec_free_context(&ifile->streams[i].dec_ctx);

    av_freep(&ifile->streams);
    ifile->nb_streams = 0;

    avformat_close_input(&ifile->fmt_ctx);
}

static int packet_sizes(const char *filename) {
    InputFile ifile = { 0 };
    int ret, i;

    ret = open_input_file(&ifile, filename);
    if (ret < 0)
        goto end;
    
    nb_streams = ifile.fmt_ctx->nb_streams;
    REALLOCZ_ARRAY_STREAM(nb_streams_frames,0,ifile.fmt_ctx->nb_streams);
    REALLOCZ_ARRAY_STREAM(nb_streams_packets,0,ifile.fmt_ctx->nb_streams);
    REALLOCZ_ARRAY_STREAM(selected_streams,0,ifile.fmt_ctx->nb_streams);
    
    const char *stream_specifier = "v";
    
    for (i = 0; i < ifile.fmt_ctx->nb_streams; i++) {
        if (stream_specifier) {
            ret = avformat_match_stream_specifier(ifile.fmt_ctx,
                                                  ifile.fmt_ctx->streams[i],
                                                  stream_specifier);
            if (ret < 0) goto end;
            else
                selected_streams[i] = ret;
            ret = 0;
        } else {
            selected_streams[i] = 1;
        }
        if (!selected_streams[i])
            ifile.fmt_ctx->streams[i]->discard = AVDISCARD_ALL;
    }

    ret = read_packet_sizes(&ifile);
    
    end:
    if (ifile.fmt_ctx)
        close_input_file(&ifile);
    av_freep(&nb_streams_frames);
    av_freep(&nb_streams_packets);
    av_freep(&selected_streams);

    return ret;
}

int main(int argc, char **argv) {
    packet_sizes("input.ts");
    return 0;
}

