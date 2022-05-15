#include<stdio.h>

struct verifier_state {
  unsigned int ins_len;
  const unsigned long long *ins;
};

_Bool bpf_verifier(struct verifier_state *);
