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

From compcert Require Import Integers.
From bpf.comm Require Import Regs rBPFValues LemmaNat.
From Coq Require Import List ZArith Lia.


(**r This folder is used to translate rBPF bytecode (int64) into each field: dst, stc, imm, ofs *)

Open Scope Z_scope.

Definition z_to_reg (z:Z): option reg :=
  if (Z.eqb z 0) then
    Some R0
  else if (Z.eqb z 1) then
    Some R1
  else if (Z.eqb z 2) then
    Some R2
  else if (Z.eqb z 3) then
    Some R3
  else if (Z.eqb z 4) then
    Some R4
  else if (Z.eqb z 5) then
    Some R5
  else if (Z.eqb z 6) then
    Some R6
  else if (Z.eqb z 7) then
    Some R7
  else if (Z.eqb z 8) then
    Some R8
  else if (Z.eqb z 9) then
    Some R9
  else if (Z.eqb z 10) then
    Some R10
  else (**r TODO: bpf verifier / verifier-invariant should ensure this branch is unreachable *)
    None.


Definition get_dst (i:int64):Z := Int64.unsigned (Int64.shru (Int64.and i (Int64.repr 0xfff)) (Int64.repr 8)).

Definition get_src (i:int64):Z := Int64.unsigned (Int64.shru (Int64.and i (Int64.repr 0xffff)) (Int64.repr 12)).

Definition int64_to_dst_reg' (ins: int64): option reg := z_to_reg (get_dst ins).

Definition int64_to_src_reg' (ins: int64): option reg := z_to_reg (get_src ins).

Definition get_opcode (ins:int64): nat := Z.to_nat (Int64.unsigned (Int64.and ins (Int64.repr 0xff))).

Definition get_offset (i:int64) := Int.sign_ext 16 (Int.repr (Int64.unsigned (Int64.shru (Int64.shl i (Int64.repr 32)) (Int64.repr 48)))).

Definition get_immediate (i1:int64) := int64_to_sint32 (Int64.shru i1 (Int64.repr 32)).
Close Scope Z_scope.

Lemma get_opcode_le_255 :
  forall i,
    0<= get_opcode i <= 255.
Proof.
  intros.
  unfold get_opcode.
  split; [lia |].
  unfold Int64.and.
  change (Int64.unsigned (Int64.repr 255)) with 255%Z.
  assert (Hc_le: (0 <= Z.land (Int64.unsigned i) 255 <= 255)%Z). {
    assert (Heq: (Int64.unsigned i) = Z.of_nat (Z.to_nat(Int64.unsigned i))). {
      rewrite Z2Nat.id.
      reflexivity.
      assert (Hrange: (0 <= Int64.unsigned i < Int64.modulus)%Z) by apply Int64.unsigned_range.
      lia.
    }
    rewrite Heq; clear.
    change 255%Z with (Z.of_nat (Z.to_nat 255%Z)) at 1 2.
    rewrite land_land.
    split.
    lia.
    assert (H: ((Nat.land (Z.to_nat (Int64.unsigned i)) (Z.to_nat 255)) <= 255)%nat). {
      rewrite Nat.land_comm.
      rewrite land_bound.
      lia.
    }
    lia.
  }
  rewrite Int64.unsigned_repr; [ | change Int64.max_unsigned with 18446744073709551615%Z; lia].

  lia.
Qed.