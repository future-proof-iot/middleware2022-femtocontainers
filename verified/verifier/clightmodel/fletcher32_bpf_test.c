#include <stdio.h>
#include <inttypes.h>
#include "verifier.h"
#include "fletcher32_bpf_simpl.h"
#include <stdlib.h>
#include <stddef.h>
#include <time.h>

int main(){
  
  printf("Hello rBPF_verifier: fletcher32 Testing\n");
  
  _Bool result;
  
  struct verifier_state st = {
    .ins_len  = sizeof(bpf_fletcher32_bpf_simpl_bin)/8,
    .ins      = (const unsigned long long *) bpf_fletcher32_bpf_simpl_bin
  };
  
  clock_t begin1 = clock();
  result = bpf_verifier(&st);
  clock_t end1 = clock();
  printf("execution time:%f\n", (double)(end1-begin1)/CLOCKS_PER_SEC);
  
  printf("rBPF_fletcher32 (dx) C result =:%d\n", result);
  printf ("End rBPF_verifier: fletcher32 Testing\n");
  return 0;
}



