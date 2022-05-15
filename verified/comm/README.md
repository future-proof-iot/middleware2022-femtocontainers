# Common Structure

This folder provides a common base for all subsequent models. i.e. the common elements of rBPF interpreter.

## File struct
- `Flag.v`: bpf flag: *BPF_OK, BPF_SUCC, BPF_ILLEGAL_...*
- `Int16.v`: defining the `char` type in Coq because CompCert only defines _Byte, Int, Int64_
- `List64.v`: representing the input bpf 64-bits as a fixed-length List, it will be translated into a C pointer type (`unsigned long long* `).
- `MemRegion.v`: defining a memory region as a record, and a fixed-length List will be translated into a C pointer type (`struct mem_region* `).
- `Regs.v`: defining the inductive `reg` type and the register map as a record, it also includes some functions that capture the specific fields from a 64-bit instruction, i.e. _dst, src, opcode, immediate, offset_.
- `rBPFAST.v`: defining some memorychunk-related functions.
- `rBPFValues.v`: defining all _Val_-comparison functions and _Val/Integers_-type casting functions.
- `State.v`: defining the rBPF state as a record and all state-related functions.
- `Monad.v`: defining a rBPF option&state monad as a record and all monadic operations.
