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

From compcert Require Import Integers Values AST Ctypes.
From Coq Require Import ZArith Lia.

From bpf.comm Require Import BinrBPF Monad LemmaNat.
From bpf.clightlogic Require Import CommonLemma.
From bpf.verifier.comm Require Import state monad.
From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.


Open Scope Z_scope.

Lemma bpf_verifier_aux2_some:
  forall st pc len op ins,
    exists b,
      bpf_verifier_aux2 pc len op ins st = Some (b ,st).
Proof.
  intros.
  unfold bpf_verifier_aux2.

  destruct nat_to_opcode.
  + destruct Int.eq.
    * unfold bpf_verifier_opcode_alu64_imm.
      unfold is_not_div_by_zero64, is_shift_range64, bindM, returnM.
      unfold is_not_div_by_zero64', is_shift_range64'.
      destruct nat_to_opcode_alu64_imm; eexists; try reflexivity.
    * unfold bpf_verifier_opcode_alu64_reg.
      unfold is_well_src, is_well_src', bindM, returnM.
      destruct nat_to_opcode_alu64_reg; eexists; try reflexivity.
  + destruct Int.eq.
    * unfold bpf_verifier_opcode_alu32_imm.
      unfold is_not_div_by_zero, is_shift_range, bindM, returnM.
      unfold is_not_div_by_zero', is_shift_range'.
      destruct nat_to_opcode_alu32_imm; eexists; try reflexivity.
    * unfold bpf_verifier_opcode_alu32_reg.
      unfold is_well_src, is_well_src', bindM, returnM.
      destruct nat_to_opcode_alu32_reg; eexists; try reflexivity.
  + destruct Int.eq.
    * unfold bpf_verifier_opcode_branch_imm.
      unfold is_dst_R0, get_offset, is_well_jump, bindM, returnM.
      unfold is_dst_R0', get_offset, is_well_jump'.
      destruct nat_to_opcode_branch_imm; eexists; try reflexivity.
    * unfold bpf_verifier_opcode_branch_reg.
      unfold get_offset, is_well_src, is_well_jump, is_well_src', is_well_jump', bindM, returnM.
      destruct nat_to_opcode_branch_reg. 12:{ exists false; reflexivity. }

      all: exists ((Int.cmpu Cle (Int.repr (get_src ins)) (Int.repr 10)) && (Int.cmpu Cle (Int.add (Int.repr (Z.of_nat pc)) (BinrBPF.get_offset ins))
           (Int.sub (Int.repr (Z.of_nat len)) (Int.repr 2))))%bool.
      all: try
      match goal with
      | |- context [(if ?X then _ else _) _] =>
        destruct X; [ rewrite Bool.andb_true_l |]; reflexivity
      end.
  + unfold bpf_verifier_opcode_load_imm.
    unfold bindM, returnM.
    destruct nat_to_opcode_load_imm; eexists; try reflexivity.
  + unfold bpf_verifier_opcode_load_reg.
    unfold is_well_src, is_well_src', bindM, returnM.
    destruct nat_to_opcode_load_reg; eexists; try reflexivity.
  + unfold bpf_verifier_opcode_store_imm.
    unfold bindM, returnM.
    destruct nat_to_opcode_store_imm; eexists; try reflexivity.
  + unfold bpf_verifier_opcode_store_reg.
    unfold is_well_src, is_well_src', bindM, returnM.
    destruct nat_to_opcode_store_reg; eexists; try reflexivity.
  + eexists; try reflexivity.
Qed.

Lemma bpf_verifier_aux_never_none:
  forall st k,
    (Z.of_nat (ins_len st) <= Int.max_unsigned) ->
    (k <= (ins_len st))%nat ->
      bpf_verifier_aux k (ins_len st) st <> None.
Proof.
  intros.
  induction k.
  - simpl.
    unfold returnM.
    intro Hfalse; inversion Hfalse.
  - assert (Hlt: (k <= ins_len st)%nat). {
      apply le_Sn_le.
      assumption.
    }
    specialize (IHk Hlt).

    assert (HltZ: Z.of_nat k <= Z.of_nat (ins_len st)). {
      rewrite Nat2Z.inj_le in Hlt.
      assumption.
    }

    simpl.
    unfold eval_ins, get_opcode, bindM, returnM.

    unfold Int.cmpu.
    destruct Int.ltu eqn: Hcond. 2:{
      apply Bool.negb_true_iff in Hcond.
      apply Cle_Zle_unsigned in Hcond.
      do 2 rewrite Int.unsigned_repr in Hcond; lia.
    }

    unfold is_well_dst, bindM, returnM.

    unfold is_well_dst'.
    destruct Int.cmpu; [| intro Hfalse; inversion Hfalse].

    assert (Haux2:
  forall st pc len op ins,
    exists b,
      bpf_verifier_aux2 pc len op ins st = Some (b ,st)) by apply bpf_verifier_aux2_some.

    specialize (Haux2 st k (ins_len st) (BinrBPF.get_opcode (state.eval_ins (Int.repr (Z.of_nat k)) st))
    (state.eval_ins (Int.repr (Z.of_nat k)) st)).
    destruct Haux2 as (b & Haux2).
    rewrite Haux2.
    destruct b; [assumption | intro Hfalse; inversion Hfalse].
Qed.

Lemma bpf_verifier_aux_some:
  forall st k,
    (Z.of_nat (ins_len st) <= Int.max_unsigned) ->
    (k <= (ins_len st))%nat ->
      exists res,
        bpf_verifier_aux k (ins_len st) st = Some (res, st).
Proof.
  intros.
  destruct bpf_verifier_aux eqn: Haux.
  destruct p.
  assert (Hst_eq: st = s). {
    clear - Haux.
    induction k; simpl in Haux.
    - unfold returnM in Haux.
      inversion Haux.
      reflexivity.
    - unfold eval_ins, is_well_dst, get_opcode, bindM, returnM in Haux.
      destruct Int.cmpu in Haux; [| inversion Haux].
      destruct is_well_dst' in Haux; [| inversion Haux; reflexivity].

      assert (Haux2:
    forall st pc len op ins,
      exists b,
        bpf_verifier_aux2 pc len op ins st = Some (b ,st)) by apply bpf_verifier_aux2_some.

      specialize (Haux2 st k (ins_len st) (BinrBPF.get_opcode (state.eval_ins (Int.repr (Z.of_nat k)) st))
      (state.eval_ins (Int.repr (Z.of_nat k)) st)).
      destruct Haux2 as (b0 & Haux2).
      rewrite Haux2 in Haux.
      destruct b0; [ apply IHk; assumption | inversion Haux; reflexivity].
  }
  subst.
  exists b; reflexivity.
  eapply bpf_verifier_aux_never_none in Haux; eauto.
  inversion Haux.
Qed.

Theorem verifier_some:
  forall st,
    (Z.of_nat (ins_len st) <= Int.max_unsigned) ->
      exists res,
        bpf_verifier st = Some (res, st).
Proof.
  intros.
  unfold bpf_verifier.
  unfold eval_ins_len, bindM, returnM.
  unfold state.eval_ins_len.
  match goal with
  | |- context[if ?X then _ else _] =>
    destruct X eqn: Hlow; [| exists false; reflexivity]
  end.
  match goal with
  | |- context[if ?X then _ else _] =>
    destruct X; [| exists false; reflexivity]
  end.

  eapply bpf_verifier_aux_some in H as Haux.
  destruct Haux as (res & Haux).
  rewrite Haux.
  destruct res.
  unfold eval_ins.
  unfold Int.cmpu.
  apply Cle_Zle_unsigned in Hlow.
  change (Int.unsigned Int.one) with 1 in Hlow.
  rewrite Int.unsigned_repr in Hlow; [| lia].
  destruct Int.ltu eqn: Hcond.
  eexists; reflexivity.

  apply Bool.negb_true_iff in Hcond.
  apply Cle_Zle_unsigned in Hcond.
  do 2 rewrite Int.unsigned_repr in Hcond; try lia.
  exists false; reflexivity.
  apply Nat.le_refl.
Qed.

Theorem verifier_never_none:
  forall st,
    (Z.of_nat (ins_len st) <= Int.max_unsigned) ->
      bpf_verifier st <> None.
Proof.
  intros.
  unfold bpf_verifier.
  unfold eval_ins_len, bindM, returnM.
  unfold state.eval_ins_len.
  match goal with
  | |- (if ?X then _ else _) _ <> _ =>
    destruct X eqn: Hlow; [| intro Hfalse; inversion Hfalse]
  end.
  match goal with
  | |- (if ?X then _ else _) _ <> _ =>
    destruct X; [| intro Hfalse; inversion Hfalse]
  end.
  apply Cle_Zle_unsigned in Hlow.
  change (Int.unsigned Int.one) with 1 in Hlow.
  rewrite Int.unsigned_repr in Hlow; [| lia].

  eapply bpf_verifier_aux_some in H as Haux.
  destruct Haux as (res & Haux).
  rewrite Haux.

  destruct res; [| intro Hfalse; inversion Hfalse].
  unfold eval_ins.
  unfold Int.cmpu.
  destruct Int.ltu eqn: Hcond.
  intro Hfalse; inversion Hfalse.

  apply Bool.negb_true_iff in Hcond.
  apply Cle_Zle_unsigned in Hcond.
  do 2 rewrite Int.unsigned_repr in Hcond; try lia.
  apply Nat.le_refl.
Qed.

From bpf.isolation Require Import VerifierOpcode VerifierInv.

Lemma verifier_aux2_inv_imply:
  forall k len op ins st
  (Hop: (op <= 255)%nat)
  (Hdst : is_well_dst' ins = true)
  (Haux2 : verifier_synthesis.bpf_verifier_aux2 k len op ins st = Some (true, st)),
    bpf_verifier_aux2 k len op ins = true.
Proof.
  unfold verifier_synthesis.bpf_verifier_aux2, bpf_verifier_aux2.
  unfold opcode_synthesis.nat_to_opcode, nat_to_opcode.
  unfold is_well_dst', is_well_dst.
  intros k len op ins st Hop Hdst.
  remember (Init.Nat.land op 7) as n.

  destruct n.
  {
    unfold bpf_verifier_opcode_load_imm, bindM, returnM.
    unfold opcode_synthesis.nat_to_opcode_load_imm, nat_to_opcode_load_imm.
    clear - Hdst.
    intro.
    do 16 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; assumption | ].
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; assumption | inversion Haux2].
  }

  destruct n.
  {
    unfold bpf_verifier_opcode_load_reg, bindM, returnM.
    unfold opcode_synthesis.nat_to_opcode_load_reg, nat_to_opcode_load_reg.
    clear - Hdst.
    unfold verifier_synthesis.is_well_src, is_well_src, is_well_src', returnM.
    unfold Int.cmpu in *.
    intro.
    do 97 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2 | ].
    rewrite Hdst, H0.
    reflexivity.
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2 | ].
    rewrite Hdst, H0.
    reflexivity.
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2 | ].
    rewrite Hdst, H0.
    reflexivity.
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2 | ].
    rewrite Hdst, H0.
    reflexivity.
    inversion Haux2.
  }

  destruct n.
  {
    unfold bpf_verifier_opcode_store_imm, bindM, returnM.
    unfold opcode_synthesis.nat_to_opcode_store_imm, nat_to_opcode_store_imm.
    clear - Hdst.
    unfold Int.cmpu in *.
    intro.
    do 98 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; assumption | ].
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; assumption | ].
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; assumption | ].
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; assumption | inversion Haux2].
  }

  destruct n.
  {
    unfold bpf_verifier_opcode_store_reg, bindM, returnM.
    unfold opcode_synthesis.nat_to_opcode_store_reg, nat_to_opcode_store_reg.
    clear - Hdst.
    unfold verifier_synthesis.is_well_src, is_well_src, is_well_src', returnM.
    unfold Int.cmpu in *.
    intro.
    do 99 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; rewrite Hdst, H0; reflexivity | ].
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; rewrite Hdst, H0; reflexivity | ].
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; rewrite Hdst, H0; reflexivity | ].
    do 7 (destruct op; [inversion Haux2|]).
    destruct op; [inversion Haux2; rewrite Hdst, H0; reflexivity | inversion Haux2].
  }

  destruct n.
  {
    symmetry in Heqn.
    rewrite nat_land_7_eq in Heqn; [ | lia].
    destruct Heqn as (m & Heqn).
    rewrite Heqn in *.
    unfold bpf_verifier_opcode_alu32_imm, bpf_verifier_opcode_alu32_reg, bindM, returnM.
    unfold nat_to_opcode_alu32_imm, nat_to_opcode_alu32_reg, nat_to_opcode_alu.
    unfold verifier_synthesis.is_not_div_by_zero, verifier_synthesis.is_shift_range, verifier_synthesis.is_well_src, is_well_src.
    unfold is_not_div_by_zero', is_shift_range', is_well_src', returnM.
    unfold Int.cmpu in *.
    unfold is_not_div_by_zero, is_shift_range.
    intro.

Ltac change_inversion_if Hi :=
    match goal with
    | H : (if ?X then _ else _) _ = _ |- _ =>
      change X with Hi in H; inversion H
    end.

    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    lia.
  }

  destruct n.
  {
    symmetry in Heqn.
    rewrite nat_land_7_eq in Heqn; [ | lia].
    destruct Heqn as (m & Heqn).
    rewrite Heqn in *.
    unfold bpf_verifier_opcode_branch_imm, bpf_verifier_opcode_branch_reg, bindM, returnM.
    unfold nat_to_opcode_branch_imm, nat_to_opcode_branch_reg, nat_to_opcode_branch.
    unfold is_dst_R0, get_offset, verifier_synthesis.is_well_jump, verifier_synthesis.is_well_src, is_well_jump, is_well_src.
    unfold is_dst_R0', is_well_jump', is_well_src', returnM.
    unfold Int.cmpu in *.
    intro.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.

Ltac destruct_inversion_match_if :=
    match goal with
    | H : match (if ?X then _ else _) _ with _ => _ end = _ |- _ =>
      destruct X; inversion H
    end.

    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *. change_inversion_if true. reflexivity.
    destruct m. simpl in *. change_inversion_if false.

    destruct m. simpl in *; change_inversion_if true. reflexivity.
    destruct m. simpl in *. change_inversion_if false.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct_inversion_match_if. rewrite Hdst, H1. reflexivity.

    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    destruct m. simpl in *; change_inversion_if true; rewrite Hdst; reflexivity.
    destruct m. simpl in *. change_inversion_if false.
    lia.
  }

  destruct n.
  {
    unfold returnM.
    intros Hfalse; inversion Hfalse.
  }

  destruct n.
  {
    symmetry in Heqn.
    rewrite nat_land_7_eq in Heqn; [ | lia].
    destruct Heqn as (m & Heqn).
    rewrite Heqn in *.
    unfold bpf_verifier_opcode_alu64_imm, bpf_verifier_opcode_alu64_reg, bindM, returnM.
    unfold nat_to_opcode_alu64_imm, nat_to_opcode_alu64_reg, nat_to_opcode_alu.
    unfold verifier_synthesis.is_not_div_by_zero64, verifier_synthesis.is_shift_range64, verifier_synthesis.is_well_src, is_well_src.
    unfold is_not_div_by_zero64', is_shift_range64', is_well_src', returnM.
    unfold Int.cmpu in *.
    unfold is_not_div_by_zero64, is_shift_range64.
    intro.

    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [ simpl in *; inversion Haux2; assumption |
      destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|]].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if true; rewrite Hdst, H0; reflexivity|].
    destruct m; [simpl in *; change_inversion_if false; rewrite Hdst, H0; reflexivity|].
    lia.
  }

  unfold returnM.
  intros Hfalse; inversion Hfalse.
Qed.

Lemma verifier_aux_inv_imply:
  forall st k,
    (Z.of_nat (ins_len st) <= Int.max_unsigned) ->
    (k <= (ins_len st))%nat ->
      verifier_synthesis.bpf_verifier_aux k (ins_len st) st = Some (true, st) ->
      bpf_verifier_aux k (ins_len st) st = true.
Proof.
  intros.
  induction k; simpl.
  - unfold returnM; reflexivity.
  - assert (Hlt: (k <= ins_len st)%nat). {
      apply le_Sn_le.
      assumption.
    }
    specialize (IHk Hlt).

    simpl in H1.
    unfold eval_ins, get_opcode, bindM, returnM in *.
    destruct Int.cmpu; [| inversion H1].
    unfold verifier_synthesis.is_well_dst, returnM in H1.
    destruct is_well_dst' eqn: Hdst; [| inversion H1].
    unfold state.eval_ins in Hdst.

    assert (Haux2:
    forall st pc len op ins,
      exists b,
        verifier_synthesis.bpf_verifier_aux2 pc len op ins st = Some (b ,st)) by apply bpf_verifier_aux2_some.

    specialize (Haux2 st k (ins_len st) (BinrBPF.get_opcode (state.eval_ins (Int.repr (Z.of_nat k)) st))
    (state.eval_ins (Int.repr (Z.of_nat k)) st)).
    destruct Haux2 as (b0 & Haux2).
    rewrite Haux2 in H1.
    destruct b0; [ specialize (IHk H1) | inversion H1].
    apply verifier_aux2_inv_imply in Haux2; auto.
    unfold state.eval_ins in Haux2.
    rewrite Haux2.
    assumption.
    assert (Hopcode: forall i : int64, (0 <= BinrBPF.get_opcode i <= 255)%nat) by apply get_opcode_le_255.
    specialize (Hopcode (state.eval_ins (Int.repr (Z.of_nat k)) st)).
    lia.
Qed.

Lemma verifier_inv_imply:
  forall st,
    (Z.of_nat (ins_len st) <= Int.max_unsigned) ->
    (ins_len st) = (List.length (ins st)) ->
      verifier_synthesis.bpf_verifier st = Some (true, st) ->
      bpf_verifier st = true.
Proof.
  unfold verifier_synthesis.bpf_verifier, bpf_verifier, eval_ins_len, state.eval_ins_len.
  unfold bindM, returnM.
  intros.
  match goal with
  | |- (if ?X then _ else _) = _ =>
    destruct X eqn: Hle_low; [ | inversion H1]
  end.
  match goal with
  | |- (if ?X then _ else _) = _ =>
    destruct X eqn: Hle_high; [ | inversion H1]
  end.

  eapply bpf_verifier_aux_some in H as Hsome; eauto.
  destruct Hsome as (res & Hsome).
  rewrite Hsome in H1.
  destruct res; [| inversion H1].

  eapply verifier_aux_inv_imply in Hsome; eauto.
  rewrite Hsome.
  unfold eval_ins in H1.
  destruct Int.cmpu; inversion H1.
  reflexivity.
Qed.

Close Scope Z_scope.