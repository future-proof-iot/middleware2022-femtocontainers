#include <stdint.h>
#include "bpf/bpfapi/helpers.h"

#define THREAD_START_KEY    0x0

typedef struct {
    uint64_t previous;  /**< previous pid */
    uint64_t next;      /**< next pid */
} pid_ctx_t;

int pid_log(pid_ctx_t *ctx)
{
    if (ctx->next != 0) {
        uint32_t counter;
        bpf_fetch_global(THREAD_START_KEY + ctx->next, &counter);
        counter++;
        bpf_store_global(THREAD_START_KEY + ctx->next, counter);
    }
    return  0;
}
