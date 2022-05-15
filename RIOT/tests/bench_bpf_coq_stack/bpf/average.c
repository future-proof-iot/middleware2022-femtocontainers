#include <stddef.h>
#include "bpf/shared.h"
#include "bpf/bpfapi/helpers.h"
#include "unaligned.h"

#define START_VALUE 0

typedef struct {
    uint32_t num_variables;
    uint32_t values[];
} averaging_ctx_t;

int average(averaging_ctx_t *ctx)
{
    uint64_t sum = 0;
    for (uint32_t i = 0; i < ctx->num_variables; i++) {
        sum += ctx->values[i];
    }
    return sum / ctx->num_variables;
}
