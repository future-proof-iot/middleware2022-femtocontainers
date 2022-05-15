# Isolation proof (Certirbpf ensures the sandboxing property)

This folder is used to prove the isolation property of the proof model (rbpf-coq interpreter).

*using the make command: `make isolation`*

There are two target thoerems:

```Coq
(**r Isolation.v *)
Theorem bpf_interpreter_preserving_inv:
  forall fuel st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hver: verifier_inv st1)
    (Hsem: bpf_interpreter fuel st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ verifier_inv st2.
       
Theorem inv_avoid_bpf_interpreter_undef:
  forall st f
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hver: verifier_inv st),
      bpf_interpreter f st <> None.     
```
where `register_inv` is the register invariant, `memory_inv` is the memory invariant for Certirbpf and `verifier_inv` is the verifier invaraint.

## File struct
- `CommonLib.v`: some common lemmas
- `AlignChunk.v`: some definitions and lemmas about **Memory Aligned**
- `RegsInv.v`: the register invariant and related lemmas
- `MemInv.v`: the memory invariant and related lemmas
- `IsolationLemma.v`: some lemmas used by the proof of the isolation property
- `Isolation.v`: two target thoerems.
