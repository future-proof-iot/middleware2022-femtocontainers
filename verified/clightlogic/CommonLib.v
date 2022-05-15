(**************************************************************************)
(*  This file is part of CertrBPF,                                        *)
(*  a formally verified rBPF verifier + interpreter + JIT in Coq.         *)
(*                                                                        *)
(*  Copyright (C) 2022 Inria                                              *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(*                                                                        *)
(**************************************************************************)

From bpf.comm Require Import rBPFValues rBPFAST Regs Flag.
From compcert Require Import Integers Values Memtype Memory AST Coqlib.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

(** common libs for clightlogic

*)

Definition id_of_reg (r:reg) : Z :=
  match r with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  | R8 => 8
  | R9 => 9
  | R10 => 10
  end.

Definition Z_of_flag (f:bpf_flag) : Z :=
  match f with
  | BPF_SUCC_RETURN  => 1
  | BPF_OK  => 0
  | BPF_ILLEGAL_INSTRUCTION => -1
  | BPF_ILLEGAL_MEM => -2
  | BPF_ILLEGAL_JUMP => -3
  | BPF_ILLEGAL_CALL => -4
  | BPF_ILLEGAL_LEN  => -5
  | BPF_ILLEGAL_REGISTER => -6
  | BPF_NO_RETURN => -7
  | BPF_OUT_OF_BRANCHES => -8
  | BPF_ILLEGAL_DIV => -9
  | BPF_ILLEGAL_SHIFT => -10
  | BPF_ILLEGAL_ALU => -11
  end.

Definition int_of_flag (f:bpf_flag)  :=
  Int.repr (Z_of_flag f).


Definition inject_bl_state (bl_state b: block) :=
  if Pos.eqb b bl_state then
    None
  else
    Some (b, 0).

Definition correct_perm (p: permission) (n: int): Prop :=
  match p with
  | Freeable => n = Int.repr 3
  | Writable => n = Int.repr 2
  | Readable => n = Int.repr 1
  | Nonempty => n = Int.repr 0
  end.

Close Scope Z_scope.