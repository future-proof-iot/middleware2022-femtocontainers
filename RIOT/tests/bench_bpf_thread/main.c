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
#include "bpf.h"
#include "bpf/shared.h"
#include "bpf/instruction.h"
#include "embUnit.h"
#include "xtimer.h"

#include "blob/bpf/thread_log.bin.h"

static uint8_t _bpf_stack[512];

/**
 *  Scheduler statistics
 */
typedef struct {
    uint64_t previous;
    uint64_t next;
} sched_ctx_t;

static void _init(void)
{
    bpf_init();
}

static void tests_bpf_run1(void)
{
    sched_ctx_t ctx = {
        .previous = 1,
        .next = 2,
    };
    bpf_t bpf = {
        .application = thread_log_bin,
        .application_len = sizeof(thread_log_bin),
        .stack = _bpf_stack,
        .stack_size = sizeof(_bpf_stack),
    };
    bpf_setup(&bpf);

    int64_t result = 0;
    uint32_t start = xtimer_now_usec();
    int res = 0;
    for (unsigned i = 0; i < 100000; i++) {
        res = bpf_execute_ctx(&bpf, &ctx, sizeof(ctx), &result);
    }
    uint32_t stop = xtimer_now_usec();

    TEST_ASSERT_EQUAL_INT(0, res);
    printf("Result: %"PRIx32"\n", (uint32_t)result);
    printf("duration: %"PRIu32" us -> %"PRIu32" us/exec\n",
           (stop - start), (stop - start)/100000);
}

Test *tests_bpf(void)
{
    EMB_UNIT_TESTFIXTURES(fixtures) {
        new_TestFixture(tests_bpf_run1),
    };

    EMB_UNIT_TESTCALLER(bpf_tests, _init, NULL, fixtures);
    return (Test*)&bpf_tests;
}

int main(void)
{
    TESTS_START();
    TESTS_RUN(tests_bpf());
    TESTS_END();

    return 0;
}
