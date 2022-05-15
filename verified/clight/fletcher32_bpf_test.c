#include <stdio.h>
#include <inttypes.h>
#include "interpreter.h"
#include "fletcher32_bpf.h"
#include "fletcher32_bpf_simpl.h"
#include <stdlib.h>
#include <stddef.h>
#include <time.h> 

uint32_t fletcher32(const uint16_t *data, size_t words)
{
    uint32_t sum1 = 0xffff, sum2 = 0xffff, sumt = 0xffff;

    while (words) {
        unsigned tlen = words > 359 ? 359 : words;
        words -= tlen;
        do {
            sumt = sum1;
            sum2 += sum1 += *data++;
        } while (--tlen);
        sum1 = (sum1 & 0xffff) + (sum1 >> 16);
        sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    }
    sum1 = (sum1 & 0xffff) + (sum1 >> 16);
    sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    return (sum2 << 16) | sum1;
}

static const unsigned char wrap_around_data[] =
        "AD3Awn4kb6FtcsyE0RU25U7f55Yncn3LP3oEx9Gl4qr7iDW7I8L6Pbw9jNnh0sE4DmCKuc"
        "d1J8I34vn31W924y5GMS74vUrZQc08805aj4Tf66HgL1cO94os10V2s2GDQ825yNh9Yuq3"
        "QHcA60xl31rdA7WskVtCXI7ruH1A4qaR6Uk454hm401lLmv2cGWt5KTJmr93d3JsGaRRPs"
        "4HqYi4mFGowo8fWv48IcA3N89Z99nf0A0H2R6P0uI4Tir682Of3Rk78DUB2dIGQRRpdqVT"
        "tLhgfET2gUGU65V3edSwADMqRttI9JPVz8JS37g5QZj4Ax56rU1u0m0K8YUs57UYG5645n"
        "byNy4yqxu7";


struct fletcher32_ctx {
  const unsigned short * data;
  uint32_t words;
};

struct fletcher32_ctx f32_ctx = {
  .data = (const unsigned short *) wrap_around_data,
  .words = sizeof(wrap_around_data)/2,
};

void print_normal_addr(struct bpf_state* st){
  printf("\n\n *********print_normal_addr*******\n\n");
  printf("sizeof(f32_ctx) = %ld\n", sizeof(f32_ctx));
  printf("sizeof(f32_ctx.data) = %ld\n", sizeof(f32_ctx.data));
  printf("sizeof(f32_ctx.words) = %ld\n", sizeof(f32_ctx.words));
  printf("sizeof(bpf_fletcher32_bpf_bin) = %ld\n", sizeof(bpf_fletcher32_bpf_bin));
  
  printf("start_f32_ctx       = %lld\n", (unsigned long long) (intptr_t) &f32_ctx);
  printf("start_f32_ctx.data  = %lld\n",  (unsigned long long) (intptr_t) &(f32_ctx.data));
  printf("start_f32_ctx.words = %d\n", f32_ctx.words);
  printf("start_f32_ctx.words = %lld\n",  (unsigned long long) (intptr_t) &(f32_ctx.words));
  
  for (int i = 0; i < 10; i++) {
  	printf("%0d:", i);
  	printf("ins64        = %lld\n", *((unsigned long long *) bpf_fletcher32_bpf_bin +i));
  }
  printf("\n\n *********print_normal_addr*******\n\n");
  
  printf("\n\n *********print_region_info*******\n\n");
  
  printf("start_ctx(physical) = %d\n", ((*st).mrs)[0].start_addr);
  printf("start_ctx (value)   = %"PRIu64"\n", *(uint64_t *) (uintptr_t)((*st).mrs)[0].start_addr);
  printf("ctx_size  = %d\n", ((*st).mrs)[0].block_size);
  printf("ctx_words = %"PRIu16"\n", (uint16_t)(intptr_t)(&(((*st).mrs)[0].start_addr))+8);
  printf("ctx_words = %"PRIu16"\n", *((uint16_t *)(uintptr_t) (((*st).mrs)[0].start_addr)+8));
  
   
  printf("start_content(physical) = %d\n", ((*st).mrs)[1].start_addr);
  printf("start_content (value)   = %"PRIu16"\n", *(uint16_t *) (uintptr_t)((*st).mrs)[1].start_addr);
  printf("content_size  = %d\n", ((*st).mrs)[1].block_size);
  
  printf("\n\n *********print_region_info*******\n\n");
}


int main(){
  
  printf("Hello rBPF_fletcher32 C code Testing:\n");
  uint32_t res0;
  
  clock_t begin0 = clock();
  res0 = fletcher32((const uint16_t *) wrap_around_data, sizeof(wrap_around_data)/2);
  clock_t end0 = clock();
  printf("execution time:%f\n", (double)(end0-begin0)/CLOCKS_PER_SEC);
  printf("rBPF_fletcher32 C result = 0x:%x\n", res0);

  printf("End rBPF_fletcher32 Testing!\n");

  

  printf ("fletcher32 start!!! \n");
  unsigned long long result;
  // adding memory_regions

  const struct memory_region mr_ctx = {
  	.start_addr = (uintptr_t) &f32_ctx,
  	.block_size = sizeof(f32_ctx),
  	.block_perm = Readable,
  	.block_ptr  = (unsigned char *) (uintptr_t) &f32_ctx
  };
  
  const struct memory_region mr_content ={
  	.start_addr = (uintptr_t) (const uint16_t *)wrap_around_data,
  	.block_size = sizeof(wrap_around_data),
  	.block_perm = Readable,
  	.block_ptr  = (unsigned char *) (uintptr_t) (const uint16_t *)wrap_around_data
  }; 

  struct memory_region my_memory_regions[] = { mr_ctx, mr_content};

  struct bpf_state st = {
    .state_pc = 0,
    .bpf_flag = vBPF_OK,
    .regsmap  = {0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU},
    .mrs_num  = 2,
    .mrs      = my_memory_regions,
    .ins_len  = sizeof(bpf_fletcher32_bpf_simpl_bin)/8,
    .ins      = (const unsigned long long *) bpf_fletcher32_bpf_simpl_bin
  };
  
  //print_normal_addr(&st);
  
  clock_t begin1 = clock();
  //for (int j = 0; j < 1000; j++) { //TODO: why a loop returns a wrong result? 
    result = bpf_interpreter(&st, 10000);
    //}
  clock_t end1 = clock();
  printf("execution time:%f\n", (double)(end1-begin1)/CLOCKS_PER_SEC);
  
  printf("rBPF_fletcher32 (dx) C result = 0x:%x\n", (unsigned int)result);
  printf ("fletcher32 end!!! \n");
  return 0;
}



