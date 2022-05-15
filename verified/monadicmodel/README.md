# The synthesis model of rBPF (optimizated but not renamed)

This folder defines a formal model of optimizated rBPF in Coq, its code style is very closed to the real original C impplementation, and extracting this one will also gain the very high performance.

This model is used in two ways:
1. renaming it and using dx to extract C code.
2. as the source model of the Coq2C refinement proof in order to avoid frequently __unfold__ renamed types/definitions in the proof.

## File struct
- `Opcode.v`: Fine-grained decoding
- `rBPFInterpreter.v`: according to the original C implemenation, we develop this version, it is optimizated comparing with the proof model.
