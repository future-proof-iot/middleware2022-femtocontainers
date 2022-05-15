# Equivalence proof (rbpf = rbpf_dx = rbpf_norename)

This folder is used to prove the equality among rbpf-coq interpreter (`model/`), rbpf-coq-dx interpreter(`src/`) and rbpf-coq-no-rename (`monadicmodel/`). 

*using the make command: `make equivalence`*

The two target thoerem are:

```Coq
(**r equivalence1.v *)
Theorem equivalence_between_formal_and_dx:
  forall f,
    Semantics.bpf_interpreter f = rBPFInterpreter.bpf_interpreter f.
    
(**r equivalence2.v *)    
Theorem equivalence_between_coq_and_dx_dx:
  forall f,
    rBPFInterpreter.bpf_interpreter f = DxInstructions.bpf_interpreter f.    
```
where `f` is a fuel to ensure that the coq functions always terminate.

## Proof idea

The equivalence proof between the later two models are simple: we only need to _unfold_ the renaming types/definitions of `DxInstructions.bpf_interpreter`, and simply _destruct_. So we mainly discuss the first equivalence proof idea:

1. proving each opcode of rbpf instructions are less or equal than 255 (because it only has 8-bits) so that if one opcode is greater than 255, we will get a contradiction in the hypothesis, then the rest proof is done!

```Coq
(**r equivalence.v *)
Lemma opcode_le_255 :
  forall st,
    (Z.to_nat (Int64.unsigned
                  (Int64.and (State.eval_ins (State.eval_pc st) st) (Int64.repr 255))))%Z <= 255.
```

2. considering the fact that the main difference between`Semantics.bpf_interpreter/Semantics.bpf_interpreter_aux` and `rBPFInterpreter.bpf_interpreter/rBPFInterpreter.bpf_interpreter_aux` is the `step` function, we prove the follow lemma.
```Coq
Lemma equivalence_between_formal_and_dx_step:
  Semantics.step = rBPFInterpreter.step.
```

- we discuss each opcode
