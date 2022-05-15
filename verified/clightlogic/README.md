# Simulation proof (From the synthesis model in Coq to the implementation model in Clight)

This folder is used to prove the translation validation theorem.

*using the make command: `make proof`*

## File struct
- `Clightlogic.v`: The **Clightlogic** framework is used to prove the simulation relation between the Coq model and the C model
- `clight_exec.v`: lemmas and functions used by our framework
- `CommonLemma.v`: all common lemmas / self-defined Ltac used by the proof
- `CommonLemmaNat.v`: all common lemmas about *Nat*
- `CommonLib.v`: all common functions used by the proof
- `CorrectRel.v`: the precondition/postcondition used by the proof
- `MatchState.v`: the simulation relation and related lemmas (e.g. update functions preserve the simulation relation).
- `//simulation/`: a folder store the current proof progress: we have proved most alu instructions (see `correct_get_opcode_alu64.v`) and all branch instructions (see `correct_get_opcode_branch.v`). We make some progress on the memory instructions (see `correct_check_mem_aux2.v`)
