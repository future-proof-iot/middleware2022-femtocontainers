/*
 * Copyright (C) 2020 Inria
 * Copyright (C) 2020 Koen Zandberg <koen@bergzand.net>
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

#include "bpf.h"
#include "bpf/instruction.h"
#include "bpf/store.h"
#include "bpf/call.h"
#include "bpf/shared.h"
#include "xtimer.h"

#ifdef MODULE_GCOAP
#include "net/gcoap.h"
#include "net/nanocoap.h"
#endif
#include "saul.h"
#include "saul_reg.h"
#include "fmt.h"

#ifdef MODULE_ZTIMER
#include "ztimer.h"
#endif

uint32_t bpf_vm_printf(bpf_t *bpf, uint32_t fmt, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    return printf((char*)(uintptr_t)fmt, a2, a3, a4, a5);
}

uint32_t bpf_vm_store_local(bpf_t *bpf, uint32_t key, uint32_t value, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)a3;
    (void)a4;
    (void)a5;
    return (uint32_t)bpf_store_update_local(bpf, key, value);
}

uint32_t bpf_vm_store_global(bpf_t *bpf, uint32_t key, uint32_t value, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;
    return (uint32_t)bpf_store_update_global(key, value);
}

uint32_t bpf_vm_fetch_local(bpf_t *bpf, uint32_t key, uint32_t value, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;
    if (bpf_store_allowed(bpf, (void*)value, sizeof(uint32_t)) < 0) {
        return -1;
    }
    return (uint32_t)bpf_store_fetch_local(bpf, key, (uint32_t*)(uintptr_t)value);
}

uint32_t bpf_vm_fetch_global(bpf_t *bpf, uint32_t key, uint32_t value, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;
    if (bpf_store_allowed(bpf, (void*)value, sizeof(uint32_t)) < 0) {
        return -1;
    }
    return (uint32_t)bpf_store_fetch_global(key, (uint32_t*)(uintptr_t)value);
}

uint32_t bpf_vm_memcpy(bpf_t *bpf, uint32_t dest_p, uint32_t src_p, uint32_t size, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a4;
    (void)a5;

    void *dest = (void *)(uintptr_t)dest_p;
    const void *src = (const void *)(uintptr_t)src_p;

    return (uintptr_t) memcpy(dest, src, size);
}

#ifdef MODULE_ZTIMER
uint32_t bpf_vm_now_ms(bpf_t *bpf, uint32_t a1, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    (void)a5;
    return ztimer_now(ZTIMER_MSEC);
}
#endif

#ifdef MODULE_SAUL_REG
uint32_t bpf_vm_saul_reg_find_nth(bpf_t *bpf, uint32_t nth, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a2;
    (void)a3;
    (void)a4;
    (void)a5;
    int pos = (int)nth;
    saul_reg_t *reg = saul_reg_find_nth(pos);
    return (uint32_t)(intptr_t)reg;
}

uint32_t bpf_vm_saul_reg_find_type(bpf_t *bpf, uint32_t type, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a2;
    (void)a3;
    (void)a4;
    (void)a5;

    saul_reg_t *reg = saul_reg_find_type(type);
    return (uint32_t)(intptr_t)reg;
}

uint32_t bpf_vm_saul_reg_read(bpf_t *bpf, uint32_t dev_p, uint32_t data_p, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;

    saul_reg_t *dev = (saul_reg_t*)(intptr_t)dev_p;
    phydat_t *data = (phydat_t*)(intptr_t)data_p;

    int res = saul_reg_read(dev, data);
    return (uint32_t)res;
}
#endif

#ifdef MODULE_GCOAP
uint32_t bpf_vm_gcoap_resp_init(bpf_t *bpf, uint32_t coap_ctx_p, uint32_t resp_code_u, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;

    bpf_coap_ctx_t *coap_ctx = (bpf_coap_ctx_t *)(intptr_t)coap_ctx_p;
    unsigned resp_code = (unsigned)resp_code_u;

    gcoap_resp_init(coap_ctx->pkt, coap_ctx->buf, coap_ctx->buf_len, resp_code);
    return 0;
}

uint32_t bpf_vm_coap_add_format(bpf_t *bpf, uint32_t coap_ctx_p, uint32_t format, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;

    bpf_coap_ctx_t *coap_ctx = (bpf_coap_ctx_t *)(intptr_t)coap_ctx_p;
    ssize_t res = coap_opt_add_format(coap_ctx->pkt, format);
    return (uint32_t)res;
}

uint32_t bpf_vm_coap_opt_finish(bpf_t *bpf, uint32_t coap_ctx_p, uint32_t flags_u, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;

    bpf_coap_ctx_t *coap_ctx = (bpf_coap_ctx_t *)(intptr_t)coap_ctx_p;
    uint16_t flags = (uint16_t)flags_u;

    ssize_t res = coap_opt_finish(coap_ctx->pkt, flags);
    return (uint32_t)res;
}

uint32_t bpf_vm_coap_get_pdu(bpf_t *bpf, uint32_t coap_ctx_p, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a2;
    (void)a3;
    (void)a4;
    (void)a5;

    bpf_coap_ctx_t *coap_ctx = (bpf_coap_ctx_t *)(intptr_t)coap_ctx_p;
    return (uint32_t)(intptr_t)((coap_pkt_t*)coap_ctx->pkt)->payload;
}
#endif

#ifdef MODULE_FMT
uint32_t bpf_vm_fmt_s16_dfp(bpf_t *bpf, uint32_t out_p, uint32_t val, uint32_t fp_digits, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a4;
    (void)a5;

    char *out = (char*)(intptr_t)out_p;
    size_t res = fmt_s16_dfp(out, (int16_t)val, (int)fp_digits);
    return (uint32_t)res;
}

uint32_t bpf_vm_fmt_u32_dec(bpf_t *bpf, uint32_t out_p, uint32_t val, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;

    char *out = (char*)(intptr_t)out_p;
    size_t res = fmt_u32_dec(out, (uint32_t)val);
    return (uint32_t)res;
}
#endif

#ifdef MODULE_ZTIMER
uint32_t bpf_vm_ztimer_now(bpf_t *bpf, uint32_t a1, uint32_t a2,
                           uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    (void)a5;
    return ztimer_now(ZTIMER_USEC);
}
uint32_t bpf_vm_ztimer_periodic_wakeup(bpf_t *bpf, uint32_t last_wakeup_p,
                                       uint32_t period,
                                       uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)bpf;
    (void)a3;
    (void)a4;
    (void)a5;

    uint32_t *last = (uint32_t*)(intptr_t)last_wakeup_p;

    ztimer_periodic_wakeup(ZTIMER_USEC, last, period);
    return 0;
}
#endif

bpf_call_t bpf_get_call(uint32_t num)
{
    switch(num) {
        case BPF_FUNC_BPF_PRINTF:
            return &bpf_vm_printf;
        case BPF_FUNC_BPF_MEMCPY:
            return &bpf_vm_memcpy;
        case BPF_FUNC_BPF_STORE_LOCAL:
            return &bpf_vm_store_local;
        case BPF_FUNC_BPF_STORE_GLOBAL:
            return &bpf_vm_store_global;
        case BPF_FUNC_BPF_FETCH_LOCAL:
            return &bpf_vm_fetch_local;
        case BPF_FUNC_BPF_FETCH_GLOBAL:
            return &bpf_vm_fetch_global;
#ifdef MODULE_GCOAP
        case BPF_FUNC_BPF_GCOAP_RESP_INIT:
            return &bpf_vm_gcoap_resp_init;
        case BPF_FUNC_BPF_COAP_OPT_FINISH:
            return &bpf_vm_coap_opt_finish;
        case BPF_FUNC_BPF_COAP_ADD_FORMAT:
            return &bpf_vm_coap_add_format;
        case BPF_FUNC_BPF_COAP_GET_PDU:
            return &bpf_vm_coap_get_pdu;
#endif
#ifdef MODULE_FMT
        case BPF_FUNC_BPF_FMT_S16_DFP:
            return bpf_vm_fmt_s16_dfp;
        case BPF_FUNC_BPF_FMT_U32_DEC:
            return bpf_vm_fmt_u32_dec;
#endif

        default:
            return NULL;
    }
}
