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

#include "femtocontainer/femtocontainer.h"
#include "shared.h"
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

uint32_t f12r_vm_memcpy(f12r_t *f12r, uint64_t *regs)
{
    (void)f12r;

    void *dest = (void *)(uintptr_t)regs[0];
    const void *src = (const void *)(uintptr_t)regs[1];

    return (uintptr_t) memcpy(dest, src, regs[2]);
}

#ifdef MODULE_SAUL_REG
uint32_t f12r_vm_saul_reg_find_nth(f12r_t *f12r, uint64_t *regs)
{
    (void)f12r;
    int pos = (int)regs[0];
    saul_reg_t *reg = saul_reg_find_nth(pos);
    return (uint32_t)(intptr_t)reg;
}

uint32_t f12r_vm_saul_reg_find_type(f12r_t *f12r, uint64_t *regs)
{
    (void)f12r;

    saul_reg_t *reg = saul_reg_find_type(regs[0]);
    return (uint32_t)(intptr_t)reg;
}

uint32_t f12r_vm_saul_reg_read(f12r_t *f12r, uint64_t *regs)
{
    (void)f12r;

    saul_reg_t *dev = (saul_reg_t*)(intptr_t)regs[0];
    phydat_t *data = (phydat_t*)(intptr_t)regs[1];

    int res = saul_reg_read(dev, data);
    return (uint32_t)res;
}
#endif

#if 0
#ifdef MODULE_GCOAP
uint32_t f12r_vm_gcoap_resp_init(f12r_t *f12r, uint32_t coap_ctx_p, uint32_t resp_code_u, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)f12r;
    (void)a3;
    (void)a4;
    (void)a5;

    f12r_coap_ctx_t *coap_ctx = (f12r_coap_ctx_t *)(intptr_t)coap_ctx_p;
    unsigned resp_code = (unsigned)resp_code_u;

    gcoap_resp_init(coap_ctx->pkt, coap_ctx->buf, coap_ctx->buf_len, resp_code);
    return 0;
}

uint32_t f12r_vm_coap_add_format(f12r_t *f12r, uint32_t coap_ctx_p, uint32_t format, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)f12r;
    (void)a3;
    (void)a4;
    (void)a5;

    f12r_coap_ctx_t *coap_ctx = (f12r_coap_ctx_t *)(intptr_t)coap_ctx_p;
    ssize_t res = coap_opt_add_format(coap_ctx->pkt, format);
    return (uint32_t)res;
}

uint32_t f12r_vm_coap_opt_finish(f12r_t *f12r, uint32_t coap_ctx_p, uint32_t flags_u, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)f12r;
    (void)a3;
    (void)a4;
    (void)a5;

    f12r_coap_ctx_t *coap_ctx = (f12r_coap_ctx_t *)(intptr_t)coap_ctx_p;
    uint16_t flags = (uint16_t)flags_u;

    ssize_t res = coap_opt_finish(coap_ctx->pkt, flags);
    return (uint32_t)res;
}

uint32_t f12r_vm_coap_get_pdu(f12r_t *f12r, uint32_t coap_ctx_p, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)f12r;
    (void)a2;
    (void)a3;
    (void)a4;
    (void)a5;

    f12r_coap_ctx_t *coap_ctx = (f12r_coap_ctx_t *)(intptr_t)coap_ctx_p;
    return (uint32_t)(intptr_t)((coap_pkt_t*)coap_ctx->pkt)->payload;
}
#endif

#ifdef MODULE_FMT
uint32_t f12r_vm_fmt_s16_dfp(f12r_t *f12r, uint32_t out_p, uint32_t val, uint32_t fp_digits, uint32_t a4, uint32_t a5)
{
    (void)f12r;
    (void)a4;
    (void)a5;

    char *out = (char*)(intptr_t)out_p;
    size_t res = fmt_s16_dfp(out, (int16_t)val, (int)fp_digits);
    return (uint32_t)res;
}

uint32_t f12r_vm_fmt_u32_dec(f12r_t *f12r, uint32_t out_p, uint32_t val, uint32_t a3, uint32_t a4, uint32_t a5)
{
    (void)f12r;
    (void)a3;
    (void)a4;
    (void)a5;

    char *out = (char*)(intptr_t)out_p;
    size_t res = fmt_u32_dec(out, (uint32_t)val);
    return (uint32_t)res;
}
#endif
#endif

#ifdef MODULE_ZTIMER
uint32_t f12r_vm_ztimer_now(f12r_t *f12r, uint64_t *regs)
{
    (void)f12r;
    (void)regs;
    return ztimer_now(ZTIMER_USEC);
}
uint32_t f12r_vm_ztimer_periodic_wakeup(f12r_t *f12r, uint64_t *regs)
{
    (void)f12r;

    uint32_t *last = (uint32_t*)(intptr_t)regs[0];

    ztimer_periodic_wakeup(ZTIMER_USEC, last, regs[1]);
    return 0;
}
#endif


f12r_call_t f12r_get_external_call(uint32_t num)
{
    switch(num) {
#ifdef MODULE_SAUL_REG
        case BPF_FUNC_BPF_SAUL_REG_FIND_NTH:
            return &f12r_vm_saul_reg_find_nth;
        case BPF_FUNC_BPF_SAUL_REG_FIND_TYPE:
            return &f12r_vm_saul_reg_find_type;
        case BPF_FUNC_BPF_SAUL_REG_READ:
            return &f12r_vm_saul_reg_read;
#endif
#if 0
#ifdef MODULE_GCOAP
        case BPF_FUNC_BPF_GCOAP_RESP_INIT:
            return &f12r_vm_gcoap_resp_init;
        case BPF_FUNC_BPF_COAP_OPT_FINISH:
            return &f12r_vm_coap_opt_finish;
        case BPF_FUNC_BPF_COAP_ADD_FORMAT:
            return &f12r_vm_coap_add_format;
        case BPF_FUNC_BPF_COAP_GET_PDU:
            return &f12r_vm_coap_get_pdu;
#endif
#ifdef MODULE_FMT
        case BPF_FUNC_BPF_FMT_S16_DFP:
            return &f12r_vm_fmt_s16_dfp;
        case BPF_FUNC_BPF_FMT_U32_DEC:
            return &f12r_vm_fmt_u32_dec;
#endif
#endif
#ifdef MODULE_ZTIMER
        case BPF_FUNC_BPF_ZTIMER_NOW:
            return &f12r_vm_ztimer_now;
        case BPF_FUNC_BPF_ZTIMER_PERIODIC_WAKEUP:
            return &f12r_vm_ztimer_periodic_wakeup;
#endif
        default:
            return NULL;
    }
}
