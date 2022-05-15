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

(**r: equivalence between bpf.model (with formal syntax + semantics) and bpf.src (for dx) *)

From Coq Require Import Logic.FunctionalExtensionality ZArith Lia List.
Import ListNotations.
From compcert Require Import Integers Values Memory Memdata.

From bpf.comm Require Import State Monad LemmaNat rBPFMonadOp.

From bpf.model Require Import Semantics.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.

(*
From bpf.equivalence Require Import switch decode_if. *)

Open Scope Z_scope.

Lemma Hrepr_eq: forall (a b:Z), (0 <= a <= 255)%Z -> (0 <= b <= 255)%Z ->
  Int.repr a = Int.repr b <-> a = b.
Proof.
  intros.
  split; intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H1.
  rewrite ! Int.Z_mod_modulus_eq in H3.
  change Int.modulus with 4294967296%Z in H3.
  rewrite ! Z.mod_small in H3.
  all: try lia.

  rewrite H1; reflexivity.
Qed.


Lemma Hrepr_neq: forall (a b:Z), (0 <= a <= 255)%Z -> (0 <= b <= 255)%Z ->
  Int.repr a <> Int.repr b <-> a <> b.
Proof.
  intros.
  split; intro.
  intro.
  apply H1.
  rewrite H2; reflexivity.
  intro.
  apply H1.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H2.
  rewrite ! Int.Z_mod_modulus_eq in H4.
  change Int.modulus with 4294967296%Z in H4.
  rewrite ! Z.mod_small in H4.
  all: lia.
Qed.


Open Scope nat_scope.

Lemma equivalence_between_check_mem:
  forall st p ck v,
    Semantics.check_mem p ck v st =rBPFInterpreter.check_mem p ck v st.
Proof.
  intros.
  unfold Semantics.check_mem, check_mem.
  unfold Semantics.is_well_chunk_bool, is_well_chunk_bool.
  unfold bindM, returnM.
  destruct ck; try reflexivity.
Qed.


Lemma equivalence_between_Semantics_and_rBPFInterpreter:
  Semantics.step = rBPFInterpreter.step.
Proof.
  unfold Semantics.step, rBPFInterpreter.step.
  unfold bindM, returnM.
  apply functional_extensionality.

  intros.
  destruct eval_pc; [|reflexivity].
  destruct p.
  destruct eval_ins; [|reflexivity].
  destruct p.
  unfold decodeM, Decode.decode.

  unfold get_opcode_ins,get_opcode, BinrBPF.get_opcode, byte_to_opcode, get_dst, int64_to_dst_reg.
  unfold eval_reg, get_src64.

  unfold bindM, returnM.

  destruct BinrBPF.int64_to_dst_reg'; [| reflexivity].

  remember (Z.to_nat (Int64.unsigned (Int64.and i0 (Int64.repr 255)))) as ins.
  assert (Hins_255: ins <= 255). {
    rewrite Heqins.
    unfold Int64.and.

    assert (Heq: (Int64.unsigned i0) = Z.of_nat (Z.to_nat(Int64.unsigned i0))). {
      rewrite Z2Nat.id.
      reflexivity.
      assert (Hrange: (0 <= Int64.unsigned i0 < Int64.modulus)%Z) by apply Int64.unsigned_range.
      lia.
    }
    rewrite Heq; clear.
    change (Int64.unsigned (Int64.repr 255)) with (Z.of_nat (Z.to_nat 255%Z)) at 1.
    rewrite LemmaNat.land_land.
    assert (H: (Nat.land (Z.to_nat (Int64.unsigned i0)) (Z.to_nat 255)) <= 255%nat). {
      rewrite Nat.land_comm.
      rewrite LemmaNat.land_bound.
      lia.
    }
    rewrite Int64.unsigned_repr; [ | change Int64.max_unsigned with 18446744073709551615%Z; lia].
    lia.
  }

  assert (Heq_int_iff: Int.eq Int.zero (Int.and (Int.repr (Z.of_nat ins)) (Int.repr 8)) = (0 =? Nat.land ins  8)). {
    assert (Hrange: Nat.land ins 8 <= 8).
    rewrite Nat.land_comm.
    rewrite land_bound. lia.
    unfold Int.and, Int.zero.
    rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
    change (Int.unsigned (Int.repr 8)) with (Z.of_nat (Z.to_nat 8%Z)).
    rewrite land_land.
    change (Z.to_nat 8%Z) with 8.
    destruct (0 =? Nat.land ins 8) eqn: Heq; [rewrite Nat.eqb_eq in Heq | rewrite Nat.eqb_neq in Heq].
    rewrite Syntax.Int_eq_true.
    apply Hrepr_eq. all: try lia.

    rewrite Syntax.Int_eq_false.
    apply Hrepr_neq. all: try lia.
  }

Ltac or_simpl Hand :=
  match goal with
  | H: ?X = Nat.land ?Y ?Z |- ?W = ?Y \/ _ =>
    destruct (W =? Y) eqn: Hand; [rewrite Nat.eqb_eq in Hand; left; assumption | rewrite Nat.eqb_neq in Hand; right ]
  end.

Ltac nat_land_compute :=
  match goal with
  | |- context [Nat.land ?X ?Y] =>
    let res := eval compute in (Nat.land X Y) in
      change (Nat.land X Y) with res; simpl
  end.

Ltac destruct_match :=
  match goal with
  | |- ?X = ?X => reflexivity
  | |- context[match match ?X with | _ => _ end with | _ => _ end] =>
    destruct X; [ try reflexivity; try destruct_match | reflexivity]
  | |- context[match match ?X with | _ => _ end with | _ => _ end] =>
    destruct X; try reflexivity; try destruct_match
  end.


Ltac nat_land_computeH :=
  match goal with
  | H: 0 <> Nat.land ?X ?Y |- _ =>
    let res := eval compute in (Nat.land X Y) in
      change (Nat.land X Y) with res in H; exfalso; apply H; reflexivity
  end.

  unfold reg64_to_reg32, State.eval_reg, get_src32, get_immediate, get_src, rBPFValues.sint32_to_vint, BinrBPF.get_immediate, rBPFValues.int64_to_sint32, int64_to_src_reg, eval_reg, reg64_to_reg32, bindM, returnM.
  unfold Decode.get_instruction_alu32_imm, Decode.get_instruction_alu32_reg.
  unfold step_opcode_alu32, get_opcode_alu32, byte_to_opcode_alu32, step_alu_binary_operation,eval_reg32, eval_src32, eval_reg, upd_reg, rBPFValues.val_intuoflongu, rBPFValues.val32_divu, rBPFValues.val32_modu, State.eval_reg, bindM, returnM.
    rewrite Heq_int_iff. clear Heqins Heq_int_iff.
    remember (Int.repr (Int64.unsigned (Int64.shru i0 (Int64.repr 32)))) as imm.

  destruct (Nat.land ins 7 =? 0) eqn: Hland0; [rewrite Nat.eqb_eq in Hland0; rewrite Hland0 | rewrite Nat.eqb_neq in Hland0].
  {
    rewrite nat_land_7_eq in Hland0; [| lia].
    destruct Hland0 as (m & Hins_eq).
    rewrite Hins_eq in *.
    unfold Decode.get_instruction_ld, step_opcode_mem_ld_imm, eval_ins_len, get_opcode_mem_ld_imm, byte_to_opcode_mem_ld_imm, eval_ins, get_immediate, upd_pc_incr,
      bindM, returnM.
    rewrite ! Nat.add_0_l in *.
    do 32 (destruct m; [nat_land_compute; try reflexivity | ]).
    destruct m; [nat_land_compute; try reflexivity | ].
    lia.
  }

  destruct (Nat.land ins 7 =? 1) eqn: Hland1; [rewrite Nat.eqb_eq in Hland1; rewrite Hland1 | rewrite Nat.eqb_neq in Hland1].
  {
    rewrite nat_land_7_eq in Hland1; [| lia].
    destruct Hland1 as (m & Hins_eq).
    rewrite Hins_eq in *.
    destruct BinrBPF.int64_to_src_reg'; [| reflexivity].
    unfold Decode.get_instruction_ldx, get_offset, get_addr_ofs, step_opcode_mem_ld_reg, get_opcode_mem_ld_reg, byte_to_opcode_mem_ld_reg,
      bindM, returnM.
      do 33 (destruct m; [nat_land_compute; try reflexivity | ]).
      lia.
  }

  destruct (Nat.land ins 7 =? 2) eqn: Hland2; [rewrite Nat.eqb_eq in Hland2; rewrite Hland2 | rewrite Nat.eqb_neq in Hland2].
  {
    rewrite nat_land_7_eq in Hland2; [| lia].
    destruct Hland2 as (m & Hins_eq).
    rewrite Hins_eq in *.
    unfold Decode.get_instruction_st, get_offset, get_addr_ofs, step_opcode_mem_st_imm, get_opcode_mem_st_imm, byte_to_opcode_mem_st_imm,
      bindM, returnM.
      do 33 (destruct m; [nat_land_compute; try reflexivity | ]).
      lia.
  }

  destruct (Nat.land ins 7 =? 3) eqn: Hland3; [rewrite Nat.eqb_eq in Hland3; rewrite Hland3 | rewrite Nat.eqb_neq in Hland3].
  {
    rewrite nat_land_7_eq in Hland3; [| lia].
    destruct Hland3 as (m & Hins_eq).
    rewrite Hins_eq in *.
    destruct BinrBPF.int64_to_src_reg'; [| reflexivity].
    unfold Decode.get_instruction_stx, BinrBPF.get_offset, get_offset, get_addr_ofs, step_opcode_mem_st_reg, get_opcode_mem_st_reg, byte_to_opcode_mem_st_reg,
      bindM, returnM.
      do 33 (destruct m; [nat_land_compute; try reflexivity | ]).
      lia.
  }

  destruct (Nat.land ins 7 =? 4) eqn: Hland4; [rewrite Nat.eqb_eq in Hland4; rewrite Hland4 | rewrite Nat.eqb_neq in Hland4].
  {
    rewrite nat_land_7_eq in Hland4; [| lia].
    destruct Hland4 as (m & Hins_eq).
    rewrite Hins_eq in *.

    destruct (0 =? Nat.land (4 + 8 * m) 8) eqn: Hand8; [rewrite Nat.eqb_eq in Hand8 | rewrite Nat.eqb_neq in Hand8].
    - destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct negb; [| reflexivity]. destruct Val.divu; try reflexivity. destruct Val.longofintu; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct negb; [| reflexivity]. destruct Val.modu; try reflexivity. destruct Val.longofintu; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.longofintu; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct Int.ltu; [| reflexivity]. destruct Val.longofint; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      lia.
    - destruct BinrBPF.int64_to_src_reg'; [| reflexivity].

      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct rBPFValues.comp_ne_32; [| reflexivity]. destruct Val.divu; try reflexivity. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct rBPFValues.comp_ne_32; [| reflexivity]. destruct Val.modu; try reflexivity. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.longofintu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct rBPFValues.compu_lt_32; [| reflexivity]. destruct Val.longofint; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      lia.
  }

Ltac destruct_if_reflexivity :=
  match goal with
  | |- ?X = ?X => reflexivity
  | |- context[(if ?X then _ else _) ] =>
    destruct X; try reflexivity
  end.

  destruct (Nat.land ins 7 =? 5) eqn: Hland5; [rewrite Nat.eqb_eq in Hland5; rewrite Hland5 | rewrite Nat.eqb_neq in Hland5].
  {
    rewrite nat_land_7_eq in Hland5; [| lia].
    destruct Hland5 as (m & Hins_eq).
    rewrite Hins_eq in *.
    unfold Decode.get_instruction_branch_imm, BinrBPF.get_offset, Decode.get_instruction_branch_reg, get_offset, eval_immediate, step_opcode_branch, get_opcode_branch, byte_to_opcode_branch, upd_pc, BinrBPF.get_offset, upd_flag,
      bindM, returnM.

    destruct (0 =? Nat.land (5 + 8 * m) 8) eqn: Hand8; [rewrite Nat.eqb_eq in Hand8 | rewrite Nat.eqb_neq in Hand8].
    - destruct m; [nat_land_compute; destruct_if_reflexivity | ].
      destruct m; [nat_land_compute; destruct_if_reflexivity | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute | ]. destruct _bpf_get_call; try reflexivity.
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity | ].
      destruct m; [inversion Hand8 | ].
      lia.
    - destruct BinrBPF.int64_to_src_reg'; [| reflexivity].

      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute; unfold State.eval_reg; destruct_if_reflexivity; destruct_if_reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      lia.
  }

  destruct (Nat.land ins 7 =? 6) eqn: Hland6; [rewrite Nat.eqb_eq in Hland6; rewrite Hland6 | rewrite Nat.eqb_neq in Hland6].
  {
    rewrite nat_land_7_eq in Hland6; [| lia].
    destruct Hland6 as (m & Hins_eq).
    rewrite Hins_eq in *.
    reflexivity.
  }

  destruct (Nat.land ins 7 =? 7) eqn: Hland7; [rewrite Nat.eqb_eq in Hland7; rewrite Hland7 | rewrite Nat.eqb_neq in Hland7].
  {
    rewrite nat_land_7_eq in Hland7; [| lia].
    destruct Hland7 as (m & Hins_eq).
    rewrite Hins_eq in *.
    unfold Decode.get_instruction_alu64_imm, Decode.get_instruction_alu64_reg, eval_immediate, step_opcode_alu64, get_opcode_alu64, byte_to_opcode_alu64, upd_reg, rBPFValues.val64_divlu, rBPFValues.val64_modlu,
      bindM, returnM.

    destruct (0 =? Nat.land (7 + 8 * m) 8) eqn: Hand8; [rewrite Nat.eqb_eq in Hand8 | rewrite Nat.eqb_neq in Hand8].
    - destruct m; [nat_land_compute; destruct Val.addl; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.subl; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.mull; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct_if_reflexivity. destruct Val.divlu; try reflexivity. destruct v; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.orl; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.andl; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct_if_reflexivity. destruct Val.shll; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct_if_reflexivity. destruct Val.shrlu; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.negl; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct_if_reflexivity. destruct Val.modlu; try reflexivity. destruct v; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m; [nat_land_compute; destruct Val.xorl; try reflexivity |].
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. destruct_if_reflexivity. destruct Val.shrl; try reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [inversion Hand8 | ].
      lia.
    - destruct BinrBPF.int64_to_src_reg'; [| reflexivity].

      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.addl; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.subl; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.mull; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. unfold State.eval_reg, Regs.val64_zero; destruct_if_reflexivity. destruct Val.divlu; try reflexivity. destruct v; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.orl; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.andl; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. unfold State.eval_reg, rBPFValues.val_intuoflongu; destruct_if_reflexivity. destruct Val.shll; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute.  unfold State.eval_reg, rBPFValues.val_intuoflongu; destruct_if_reflexivity. destruct Val.shrlu; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. unfold State.eval_reg, Regs.val64_zero; destruct_if_reflexivity. destruct Val.modlu; try reflexivity. destruct v; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. destruct Val.xorl; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. unfold State.eval_reg. destruct Regs.eval_regmap; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. unfold State.eval_reg, rBPFValues.val_intuoflongu; destruct_if_reflexivity. destruct Val.shrl; try reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      destruct m.
      { nat_land_compute. reflexivity. }
      destruct m; [nat_land_computeH |].
      lia.
  }

  exfalso.

  remember (Nat.land ins 7) as Hand7.
  assert (Hand7_le: Hand7 <= 7). {
    rewrite HeqHand7.
    rewrite Nat.land_comm.
    rewrite land_bound.
    lia.
  }

  lia.
Qed.


Close Scope nat_scope.

Lemma equivalence_between_formal_and_dx_aux:
  forall f,
    Semantics.bpf_interpreter_aux f = rBPFInterpreter.bpf_interpreter_aux f.
Proof.
  unfold Semantics.bpf_interpreter_aux, rBPFInterpreter.bpf_interpreter_aux.
  rewrite equivalence_between_Semantics_and_rBPFInterpreter.
  reflexivity.
Qed.

Theorem equivalence_between_formal_and_dx:
  forall f,
    Semantics.bpf_interpreter f = rBPFInterpreter.bpf_interpreter f.
Proof.
  intros.
  unfold Semantics.bpf_interpreter, rBPFInterpreter.bpf_interpreter.
  rewrite equivalence_between_formal_and_dx_aux.
  reflexivity.
Qed.

Close Scope Z_scope.