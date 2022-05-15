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
 * @brief       Tests f12r virtual machine
 *
 * @author      Koen Zandberg <koen@bergzand.net>
 *
 * @}
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include "femtocontainer/femtocontainer.h"
#include "shared.h"
#include "embUnit.h"
#include "xtimer.h"

#include "blob/application/fletcher32_fc.bin.h"

static const unsigned char __attribute__((aligned(sizeof(uint16_t)))) wrap_around_data[] =
        "AD3Awn4kb6FtcsyE0RU25U7f55Yncn3LP3oEx9Gl4qr7iDW7I8L6Pbw9jNnh0sE4DmCKuc"
        "d1J8I34vn31W924y5GMS74vUrZQc08805aj4Tf66HgL1cO94os10V2s2GDQ825yNh9Yuq3"
        "QHcA60xl31rdA7WskVtCXI7ruH1A4qaR6Uk454hm401lLmv2cGWt5KTJmr93d3JsGaRRPs"
        "4HqYi4mFGowo8fWv48IcA3N89Z99nf0A0H2R6P0uI4Tir682Of3Rk78DUB2dIGQRRpdqVT"
        "tLhgfET2gUGU65V3edSwADMqRttI9JPVz8JS37g5QZj4Ax56rU1u0m0K8YUs57UYG5645n"
        "byNy4yqxu7";

static uint8_t _f12r_stack[512];

typedef struct {
    __bpf_shared_ptr(const uint16_t *, data);
    uint32_t words;
} fletcher32_ctx_t;

static void tests_f12r_run1(void)
{
    fletcher32_ctx_t ctx = {
        .data = (const uint16_t*)(uintptr_t) wrap_around_data,
        .words = sizeof(wrap_around_data)/2,
    };
    f12r_t femtoc = {
        .application = fletcher32_fc_bin,
        .application_len = sizeof(fletcher32_fc_bin),
        .stack = _f12r_stack,
        .stack_size = sizeof(_f12r_stack),
    };
    f12r_mem_region_t region;
    printf("f12r context size: %u, memory region size: %u\n", (unsigned)sizeof(f12r_t), (unsigned)sizeof(f12r_mem_region_t));
    f12r_setup(&femtoc);

    f12r_add_region(&femtoc, &region,
            (void*)wrap_around_data, sizeof(wrap_around_data), FC_MEM_REGION_READ);
    int64_t result = 0;
    uint32_t start = xtimer_now_usec();
    int res = 0;
    for (unsigned i = 0; i < 1000; i++) {
        res = f12r_execute_ctx(&femtoc, &ctx, sizeof(ctx), &result);
    }
    uint32_t stop = xtimer_now_usec();

    TEST_ASSERT_EQUAL_INT(0, res);
    TEST_ASSERT_EQUAL_INT(0x5bac8c3d, (uint32_t)result);
    printf("Result: %"PRIx32"\n", (uint32_t)result);
    printf("duration: %"PRIu32" us -> %"PRIu32" us/exec\n",
           (stop - start), (stop - start)/1000);
}

Test *tests_f12r(void)
{
    EMB_UNIT_TESTFIXTURES(fixtures) {
        new_TestFixture(tests_f12r_run1),
    };

    EMB_UNIT_TESTCALLER(f12r_tests, NULL, NULL, fixtures);
    return (Test*)&f12r_tests;
}

int main(void)
{
    TESTS_START();
    TESTS_RUN(tests_f12r());
    TESTS_END();

    return 0;
}
