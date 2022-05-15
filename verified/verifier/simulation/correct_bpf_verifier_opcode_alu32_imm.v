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
From bpf.verifier.simulation Require Import correct_is_not_div_by_zero correct_is_shift_range.


(**
Check bpf_verifier_opcode_alu32_imm.
bpf_verifier_opcode_alu32_imm
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Definition opcode_alu32_imm_if (op: nat) : opcode_alu32_imm :=
  if Nat.eqb op 4%nat then ADD32_IMM
  else if Nat.eqb op 20%nat then SUB32_IMM
  else if Nat.eqb op 36%nat then MUL32_IMM
  else if Nat.eqb op 52%nat then DIV32_IMM
  else if Nat.eqb op 68%nat then OR32_IMM
  else if Nat.eqb op 84%nat then AND32_IMM
  else if Nat.eqb op 100%nat then LSH32_IMM
  else if Nat.eqb op 116%nat then RSH32_IMM
  else if Nat.eqb op 132%nat then NEG32_IMM
  else if Nat.eqb op 148%nat then MOD32_IMM
  else if Nat.eqb op 164%nat then XOR32_IMM
  else if Nat.eqb op 180%nat then MOV32_IMM
  else if Nat.eqb op 196%nat then ARSH32_IMM
  else ALU32_IMM_ILLEGAL.

Lemma opcode_alu32_imm_eqb_eq : forall a b,
    opcode_alu32_imm_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_alu32_imm :
  forall (E: nat -> opcode_alu32_imm)
         (F: nat -> opcode_alu32_imm) n,
    ((fun n => opcode_alu32_imm_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_alu32_imm_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_alu32_imm_if_same:
  forall (op: nat),
    (op <= 255)%nat ->
    nat_to_opcode_alu32_imm op = opcode_alu32_imm_if op.
Proof.
  intros.
  unfold nat_to_opcode_alu32_imm, opcode_alu32_imm_if.
  apply opcode_alu32_imm_eqb_eq.
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

Lemma bpf_verifier_opcode_alu32_imm_match:
  forall op
    (Hop: (op <= 255)%nat)
    (Halu : nat_to_opcode_alu32_imm op = ALU32_IMM_ILLEGAL),
        4   <> (Z.of_nat op) /\
        20  <> (Z.of_nat op) /\
        36  <> (Z.of_nat op) /\
        52  <> (Z.of_nat op) /\
        68  <> (Z.of_nat op) /\
        84  <> (Z.of_nat op) /\
        100 <> (Z.of_nat op) /\
        116 <> (Z.of_nat op) /\
        132 <> (Z.of_nat op) /\
        148 <> (Z.of_nat op) /\
        164 <> (Z.of_nat op) /\
        180 <> (Z.of_nat op) /\
        196 <> (Z.of_nat op).
Proof.
  intros.
  rewrite byte_to_opcode_alu32_imm_if_same in Halu; auto.
  unfold opcode_alu32_imm_if in Halu.
  change 4   with (Z.of_nat 4%nat).
  change 20  with (Z.of_nat 20%nat).
  change 36  with (Z.of_nat 36%nat).
  change 52  with (Z.of_nat 52%nat).
  change 68  with (Z.of_nat 68%nat).
  change 84  with (Z.of_nat 84%nat).
  change 100 with (Z.of_nat 100%nat).
  change 116 with (Z.of_nat 116%nat).
  change 132 with (Z.of_nat 132%nat).
  change 148 with (Z.of_nat 148%nat).
  change 164 with (Z.of_nat 164%nat).
  change 180 with (Z.of_nat 180%nat).
  change 196 with (Z.of_nat 196%nat).
Ltac simpl_neq :=
  let Hfalse := fresh "Hfalse" in
  match goal with
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
  repeat simpl_neq.
Qed.


Section Bpf_verifier_opcode_alu32_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_alu32_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_alu32_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (opcode_correct x))
     (dcons (fun x => StateLess _ (int64_correct x))
      (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_opcode_alu32_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_alu32_imm.
    simpl. (*
    unfold nat_to_opcode_alu32_reg. *)
    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD32 => bindM (upd_reg ... *)
    unfold INV.
    destruct nat_to_opcode_alu32_imm eqn: Halu. (**r case discussion on each alu32_instruction *)
    - (**r ADD32_IMM *)
      eapply correct_statement_switch with (n:= 4).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 4%nat). {
          clear - Halu.
          do 4 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 192 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 4) with 4 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r SUB32_IMM *)
      eapply correct_statement_switch with (n:= 20).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 20%nat). {
          clear - Halu.
          do 20 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 176 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 20) with 20 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MUL32_IMM *)
      eapply correct_statement_switch with (n:= 36).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 36%nat). {
          clear - Halu.
          do 36 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 160 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 36) with 36 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r DIV32_IMM *)
      eapply correct_statement_switch with (n:= 52).
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
        intros.
        get_invariant _b.
        unfold eval_inv, correct_is_not_div_by_zero.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 52%nat). {
          clear - Halu.
          do 52 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 144 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 52) with 52 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r OR32_IMM *)
      eapply correct_statement_switch with (n:= 68).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 68%nat). {
          clear - Halu.
          do 68 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 128 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 68) with 68 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r AND32_IMM *)
      eapply correct_statement_switch with (n:= 84).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 84%nat). {
          clear - Halu.
          do 84 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 112 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 84) with 84 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LSH32_IMM *)
      eapply correct_statement_switch with (n:= 100).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v:: (Vint (Int.repr 32)) ::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        unfold eval_inv in c1.
        split; [assumption |].
        unfold uint32_correct.
        split;[ split;[reflexivity | apply Int.unsigned_range_2] |constructor].

        intros.
        correct_forward.
        get_invariant _b.
        unfold eval_inv, correct_is_shift_range.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 100%nat). {
          clear - Halu.
          do 100 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 96 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 100) with 100 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RSH32_IMM *)
      eapply correct_statement_switch with (n:= 116).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v:: (Vint (Int.repr 32)) ::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        unfold eval_inv in c1.
        split; [assumption |].
        unfold uint32_correct.
        split;[ split;[reflexivity | apply Int.unsigned_range_2] |constructor].

        intros.
        correct_forward.
        intros.
        get_invariant _b.
        unfold eval_inv, correct_is_shift_range.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 116%nat). {
          clear - Halu.
          do 116 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 80 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 116) with 116 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r NEG32_IMM *)
      eapply correct_statement_switch with (n:= 132).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 132%nat). {
          clear - Halu.
          do 132 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 64 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 132) with 132 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOD32_IMM *)
      eapply correct_statement_switch with (n:= 148).
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
        intros.
        get_invariant _b.
        unfold eval_inv, correct_is_not_div_by_zero.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 148%nat). {
          clear - Halu.
          do 148 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 48 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 148) with 148 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r XOR32_IMM *)
      eapply correct_statement_switch with (n:= 164).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 164%nat). {
          clear - Halu.
          do 164 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 32 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 164) with 164 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOV32_IMM *)
      eapply correct_statement_switch with (n:= 180).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 180%nat). {
          clear - Halu.
          do 180 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 180) with 180 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ARSH32_IMM *)
      eapply correct_statement_switch with (n:= 196).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _ins.
        exists (v:: (Vint (Int.repr 32)) ::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        unfold eval_inv in c1.
        split; [assumption |].
        unfold uint32_correct.
        split;[ split;[reflexivity | apply Int.unsigned_range_2] |constructor].

        intros.
        correct_forward.
        intros.
        get_invariant _b.
        unfold eval_inv, correct_is_shift_range.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 196%nat). {
          clear - Halu.
          do 196 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 196) with 196 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ALU32_IMM_ILLEGAL *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold eval_inv, opcode_correct in c1.
        destruct c1 as (c1 & Hc1_range).
        exists (Z.of_nat c).
        split.
        unfold exec_expr.
        rewrite p0.
        rewrite c1.
        reflexivity.
        split.

        change Int.modulus with 4294967296.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        apply bpf_verifier_opcode_alu32_imm_match in Halu; auto.
        destruct Halu as (Hfirst & Halu). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Halu; rewrite Halu; clear Halu.
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

End Bpf_verifier_opcode_alu32_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_alu32_imm.
