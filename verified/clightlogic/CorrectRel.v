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

From bpf.comm Require Import rBPFAST List64 MemRegion Regs Flag.

From bpf.monadicmodel Require Import Opcode.

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CommonLib.

Open Scope Z_scope.

Definition int64_correct (x:int64) (v: val) :=
  Vlong x = v.

Definition val64_correct (x:val) (v: val) :=
  x = v /\ exists vl, x = Vlong vl.

Definition val32_correct (x:val) (v: val) :=
  x = v /\ exists vi, x = Vint vi.

Definition sint32_correct (x: int) (v: val) :=
  Vint x = v /\ Int.min_signed <= Int.signed x <= Int.max_signed.

Definition uint32_correct (x: int) (v: val) :=
  Vint x = v /\ 0 <= Int.unsigned x <= Int.max_unsigned.

Definition nat_correct (x: nat) (v: val) :=
  Vint (Int.repr (Z.of_nat x)) = v /\ Z.of_nat x <= Int.max_unsigned.

Definition reg_correct (r: reg) (v: val) :=
    v = Vint (Int.repr (id_of_reg r)).

Definition match_chunk (x : memory_chunk) (b: val) :=
  b = memory_chunk_to_valu32 x.

Definition flag_correct (f: bpf_flag) (v: val) :=
  v = Vint (int_of_flag f).


Definition stateless {A St: Type} (f : A -> val -> Prop) := fun x => StateLess St (f x).
Definition statefull {A St: Type} (f : A -> val -> St -> mem -> Prop) := fun x => StateFull St (f x).

Definition perm_correct (p: permission) (n: val): Prop :=
  match p with
  | Freeable => n = Vint (Int.repr 3)
  | Writable => n = Vint (Int.repr 2)
  | Readable => n = Vint (Int.repr 1)
  | Nonempty => n = Vint (Int.repr 0)
  end.

Definition correct_perm (p: permission) (n: int): Prop :=
  match p with
  | Freeable => n = Int.repr 3
  | Writable => n = Int.repr 2
  | Readable => n = Int.repr 1
  | Nonempty => n = Int.repr 0
  end.

(**r just a copy from clightlogic *)
Definition bool_correct (b:bool) (v:val) :=
  v = Vint (if b then Integers.Int.one else Integers.Int.zero).
Close Scope Z_scope.



Open Scope nat_scope.
Definition opcode_correct (x: nat) (v: val) :=
   Vint (Int.repr (Z.of_nat x)) = v /\ x <= 255.

Definition opcode_and_07_correct (x: nat) (v: val) :=
   Vint (Int.repr (Z.of_nat (Nat.land x 0x07))) = v /\ x <= 255.
Close Scope nat_scope.
