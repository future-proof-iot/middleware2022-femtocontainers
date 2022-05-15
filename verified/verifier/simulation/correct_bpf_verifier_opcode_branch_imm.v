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

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.
From bpf.verifier.simulation Require Import correct_bpf_verifier_get_offset correct_is_well_jump correct_is_dst_R0.


(**
Check bpf_verifier_opcode_branch_imm.
bpf_verifier_opcode_branch_imm
     : nat -> nat -> nat -> int64 -> M bool

*)
Open Scope Z_scope.

Definition opcode_branch_imm_if (op: nat) : opcode_branch_imm :=
  if Nat.eqb op 5%nat then JA_IMM
  else if Nat.eqb op 21%nat then JEQ_IMM
  else if Nat.eqb op 37%nat then JGT_IMM
  else if Nat.eqb op 53%nat then JGE_IMM
  else if Nat.eqb op 69%nat then JSET_IMM
  else if Nat.eqb op 85%nat then JNE_IMM
  else if Nat.eqb op 101%nat then JSGT_IMM
  else if Nat.eqb op 117%nat then JSGE_IMM
  else if Nat.eqb op 133%nat then CALL_IMM
  else if Nat.eqb op 149%nat then RET_IMM
  else if Nat.eqb op 165%nat then JLT_IMM
  else if Nat.eqb op 181%nat then JLE_IMM
  else if Nat.eqb op 197%nat then JSLT_IMM
  else if Nat.eqb op 213%nat then JSLE_IMM
  else JMP_IMM_ILLEGAL_INS.

Lemma opcode_branch_imm_eqb_eq : forall a b,
    opcode_branch_imm_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_branch_imm :
  forall (E: nat -> opcode_branch_imm)
         (F: nat -> opcode_branch_imm) n,
    ((fun n => opcode_branch_imm_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_branch_imm_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_branch_imm_if_same:
  forall (op: nat),
    (op <= 255)%nat ->
    nat_to_opcode_branch_imm op = opcode_branch_imm_if op.
Proof.
  intros.
  unfold nat_to_opcode_branch_imm, opcode_branch_imm_if.
  apply opcode_branch_imm_eqb_eq.
  match goal with
  | |- ?A = true => set (P := A)
  end.
  pattern op in P.
  match goal with
  | P := ?F op |- _=>
      apply (Forall_exec_spec F 255)
  end.
  vm_compute.
  reflexivity.
  assumption.
Qed.

Lemma bpf_verifier_opcode_branch_imm_match:
  forall op
    (Hop: (op <= 255)%nat)
    (Halu : nat_to_opcode_branch_imm op = JMP_IMM_ILLEGAL_INS),
        5   <> (Z.of_nat op) /\
        21  <> (Z.of_nat op) /\
        37  <> (Z.of_nat op) /\
        53  <> (Z.of_nat op) /\
        69  <> (Z.of_nat op) /\
        85  <> (Z.of_nat op) /\
        101 <> (Z.of_nat op) /\
        117 <> (Z.of_nat op) /\
        133 <> (Z.of_nat op) /\
        149 <> (Z.of_nat op) /\
        165 <> (Z.of_nat op) /\
        181 <> (Z.of_nat op) /\
        197 <> (Z.of_nat op) /\
        213 <> (Z.of_nat op).
Proof.
  intros.
  rewrite byte_to_opcode_branch_imm_if_same in Halu; auto.
  unfold opcode_branch_imm_if in Halu.
  change 5   with (Z.of_nat 5%nat).
  change 21  with (Z.of_nat 21%nat).
  change 37  with (Z.of_nat 37%nat).
  change 53  with (Z.of_nat 53%nat).
  change 69  with (Z.of_nat 69%nat).
  change 85  with (Z.of_nat 85%nat).
  change 101 with (Z.of_nat 101%nat).
  change 117 with (Z.of_nat 117%nat).
  change 133 with (Z.of_nat 133%nat).
  change 149 with (Z.of_nat 149%nat).
  change 165 with (Z.of_nat 165%nat).
  change 181 with (Z.of_nat 181%nat).
  change 197 with (Z.of_nat 197%nat).
  change 213 with (Z.of_nat 213%nat).

  repeat match goal with
  | H : (if ?X then _ else _) = _ |- _ /\ _ =>
    split; [destruct X eqn: Hnew; [inversion H |
      rewrite Nat.eqb_neq in Hnew;
      intro Hfalse; apply Hnew;
      symmetry in Hfalse;
      apply Nat2Z.inj in Hfalse;
      assumption]
    | destruct X eqn: Hnew; [inversion H| clear Hnew]]
  | H : (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Hnew; [inversion H |
      rewrite Nat.eqb_neq in Hnew;
      intro Hfalse; apply Hnew;
      symmetry in Hfalse;
      apply Nat2Z.inj in Hfalse;
      assumption]
  end.
Qed.

Section Bpf_verifier_opcode_branch_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (nat:Type); (nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_branch_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_branch_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (nat_correct x))
      (dcons (fun x => StateLess _ (nat_correct x))
        (dcons (fun x => StateLess _ (opcode_correct x))
          (dcons (fun x => StateLess _ (int64_correct x))
            (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_opcode_branch_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_branch_imm.
    simpl.
    unfold INV.
    destruct nat_to_opcode_branch_imm eqn: Hbranch. (**r case discussion on each branch_instruction *)
    - (**r JA_IMM *)
      eapply correct_statement_switch with (n:= 5).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 5%nat). {
          clear - Hbranch.
          do 5 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 208 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 5) with 5 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JEQ_IMM *)
      eapply correct_statement_switch with (n:= 21).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 21%nat). {
          clear - Hbranch.
          do 21 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 192 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 21) with 21 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JGT_IMM *)
      eapply correct_statement_switch with (n:= 37).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition .
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 37%nat). {
          clear - Hbranch.
          do 37 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 176 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 37) with 37 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JGE_IMM *)
      eapply correct_statement_switch with (n:= 53).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 53%nat). {
          clear - Hbranch.
          do 53 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 160 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 53) with 53 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JLT_IMM *)
      eapply correct_statement_switch with (n:= 165).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 165%nat). {
          clear - Hbranch.
          do 165 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 48 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 165) with 165 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JLE_IMM *)
      eapply correct_statement_switch with (n:= 181).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 181%nat). {
          clear - Hbranch.
          do 181 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 32 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 181) with 181 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSET_IMM *)
      eapply correct_statement_switch with (n:= 69).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 69%nat). {
          clear - Hbranch.
          do 69 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 144 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 69) with 69 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JNE_IMM *)
      eapply correct_statement_switch with (n:= 85).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 85%nat). {
          clear - Hbranch.
          do 85 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 128 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 85) with 85 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSGT_IMM *)
      eapply correct_statement_switch with (n:= 101).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 101%nat). {
          clear - Hbranch.
          do 101 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 112 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 101) with 101 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSGE_IMM *)
      eapply correct_statement_switch with (n:= 117).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 117%nat). {
          clear - Hbranch.
          do 117 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 96 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 117) with 117 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSLT_IMM *)
      eapply correct_statement_switch with (n:= 197).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 197%nat). {
          clear - Hbranch.
          do 197 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 16 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 197) with 197 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSLE_IMM *)
      eapply correct_statement_switch with (n:= 213).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.

        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 213%nat). {
          clear - Hbranch.
          do 213 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 213) with 213 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r CALL_IMM *)
      eapply correct_statement_switch with (n:= 133).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_dst_R0.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 133%nat). {
          clear - Hbranch.
          do 133 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 80 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 133) with 133 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RET_IMM *)
      eapply correct_statement_switch with (n:= 149).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_dst_R0.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 149%nat). {
          clear - Hbranch.
          do 149 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 64 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 149) with 149 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JMP_IMM_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (c3 & Hc3_range).
        exists (Z.of_nat c1).
        split.
        unfold exec_expr.
        rewrite p0.
        rewrite <- c3.
        reflexivity.
        split.

        change Int.modulus with 4294967296.
        change Int.max_unsigned with 4294967295 in Hc3_range.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        apply bpf_verifier_opcode_branch_imm_match in Hbranch; auto.
        destruct Hbranch as (Hfirst & Hbranch). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Hbranch; rewrite Hbranch; clear Hbranch.
        (* default *)
        simpl.
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 0)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
Qed.

End Bpf_verifier_opcode_branch_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_branch_imm.
