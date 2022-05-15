# The proof model of rBPF

This folder provides the formal syntax & semantics of the rBPF instruction set (78 instructions: alu+branch+load+store).

## File struct
- `Syntax.v`: the formal syntax of the rBPF instruction set
- `Decode.v`: Coarse-grained decoding: from a rBPF binaary instruction (_int64_) to all fields (_dst, src, opcode, etc_)
- `Semantics.v`: the formal semantics of the rBPF instruction set (the monadic function `step`) and the rBPF interpreter.
