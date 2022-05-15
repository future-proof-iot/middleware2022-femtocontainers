/*
 * Copyright (C) 2020 Inria
 * Copyright (C) 2020 Koen Zandberg <koen@bergzand.net>
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     tests
 * @{
 *
 * @file
 * @brief       Tests bpf virtual machine
 *
 * @author      Koen Zandberg <koen@bergzand.net>
 *
 * @}
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include "embUnit.h"
#include "timex.h"
#include "ztimer.h"
#include "unaligned.h"
#include "thread.h"
#include "ps.h"

#if BPF_COQ
#include "bpf.h"
#include "interpreter.h"
#include "bpf/shared.h"
#include "bpf/instruction.h"
#elif FEMTO
#include "femtocontainer/femtocontainer.h"
#else
#include "bpf.h"
#include "bpf/shared.h"
#include "bpf/instruction.h"
#endif

#include "blob/bpf/average.bin.h"

typedef struct {
    uint32_t num_variables;
    uint32_t values[NUM_VARIABLES];
} averaging_ctx_t;

static uint8_t _bpf_stack[512];
static char _test_stack[2048];
mutex_t mtx;

static averaging_ctx_t ctx = { .num_variables = 5 };
#if BPF_COQ
static struct memory_region mr_ctx = {.start_addr = (uintptr_t)&ctx,
                                        .block_size = sizeof(ctx),
                                        .block_perm = Readable,
                                        .block_ptr = (unsigned char *)(uintptr_t)&ctx};

static struct memory_region mr_stack = {.start_addr = (uintptr_t)_bpf_stack,
                                        .block_size = sizeof(_bpf_stack),
                                        .block_perm = Freeable,
                                        .block_ptr = _bpf_stack};
#endif

#if BPF_COQ
static void *_run(void *arg)
{
    struct bpf_state *st = (struct bpf_state *)arg;
    bpf_interpreter(st, 10000);
    mutex_unlock(&mtx);
    return NULL;
}

#elif FEMTO

static void *_run(void *arg)
{
    f12r_t *bpf = (f12r_t*)arg;
    int64_t res;
    f12r_execute_ctx(bpf, &ctx, sizeof(ctx), &res);
    (void)res;
    mutex_unlock(&mtx);
    return NULL;
}

#else
static void *_run(void *arg)
{
    bpf_t *bpf = (bpf_t*)arg;
    int64_t res;
    bpf_execute_ctx(bpf, &ctx, sizeof(ctx), &res);
    (void)res;
    mutex_unlock(&mtx);
    return NULL;
}
#endif


int main(void)
{
#if BPF_COQ
    struct memory_region memory_regions[] = { mr_ctx, mr_stack };
    rbpf_header_t *header = (rbpf_header_t*)average_bin;
    const void * text = (uint8_t*)header + sizeof(rbpf_header_t) + header->data_len + header->rodata_len;

    struct bpf_state bpf = {
        .state_pc = 0,
        .regsmap = {0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, (intptr_t)_bpf_stack+512},
        .bpf_flag = vBPF_OK,
        .mrs = memory_regions,
        .mrs_num = ARRAY_SIZE(memory_regions),
        .ins = text,
        .ins_len = header->text_len,
    };
    size_t context_size = sizeof(bpf) + sizeof(memory_regions);
#elif FEMTO
    f12r_t bpf = {
        .application = (uint8_t*)average_bin,
        .application_len = sizeof(average_bin),
        .stack = _bpf_stack,
        .stack_size = sizeof(_bpf_stack),
    };
    f12r_setup(&bpf);
    size_t context_size = sizeof(bpf);

#else
    bpf_t bpf = {
        .application = (uint8_t*)average_bin,
        .application_len = sizeof(average_bin),
        .stack = _bpf_stack,
        .stack_size = sizeof(_bpf_stack),
    };
    bpf_setup(&bpf);
    size_t context_size = sizeof(bpf);
#endif
    mutex_lock(&mtx);
    kernel_pid_t pid = thread_create(_test_stack, sizeof(_test_stack), (THREAD_PRIORITY_MAIN + 1),
                  THREAD_CREATE_STACKTEST | THREAD_CREATE_WOUT_YIELD, _run, &bpf, "bpf_test");
    thread_t *t = thread_get(pid);
    size_t used_before = thread_get_stacksize(t) - (size_t)thread_measure_stack_free(_test_stack);
    mutex_lock(&mtx);
    size_t used_after = thread_get_stacksize(t) - (size_t)thread_measure_stack_free(_test_stack);
    ps();
    printf("stack used before: %u, after: %u. Diff: %u. Context: %u\n",
            used_before, used_after,
            used_after - used_before, context_size);
    return 0;
}
