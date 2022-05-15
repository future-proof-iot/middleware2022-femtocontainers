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
From bpf.verifier.simulation Require Import correct_is_not_div_by_zero64 correct_is_shift_range64.


(**
Check bpf_verifier_opcode_alu64_imm.
bpf_verifier_opcode_alu64_imm
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Definition opcode_alu64_imm_if (op: nat) : opcode_alu64_imm :=
  if Nat.eqb op 7%nat then ADD64_IMM
  else if Nat.eqb op 23%nat then SUB64_IMM
  else if Nat.eqb op 39%nat then MUL64_IMM
  else if Nat.eqb op 55%nat then DIV64_IMM
  else if Nat.eqb op 71%nat then OR64_IMM
  else if Nat.eqb op 87%nat then AND64_IMM
  else if Nat.eqb op 103%nat then LSH64_IMM
  else if Nat.eqb op 119%nat then RSH64_IMM
  else if Nat.eqb op 135%nat then NEG64_IMM
  else if Nat.eqb op 151%nat then MOD64_IMM
  else if Nat.eqb op 167%nat then XOR64_IMM
  else if Nat.eqb op 183%nat then MOV64_IMM
  else if Nat.eqb op 199%nat then ARSH64_IMM
  else ALU64_IMM_ILLEGAL.

Lemma opcode_alu64_imm_eqb_eq : forall a b,
    opcode_alu64_imm_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_alu64_imm :
  forall (E: nat -> opcode_alu64_imm)
         (F: nat -> opcode_alu64_imm) n,
    ((fun n => opcode_alu64_imm_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_alu64_imm_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_alu64_imm_if_same:
  forall (op: nat),
    (op <= 255)%nat ->
    nat_to_opcode_alu64_imm op = opcode_alu64_imm_if op.
Proof.
  intros.
  unfold nat_to_opcode_alu64_imm, opcode_alu64_imm_if.
  apply opcode_alu64_imm_eqb_eq.
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

Lemma bpf_verifier_opcode_alu64_imm_match:
  forall op
    (Hop: (op <= 255)%nat)
    (Halu : nat_to_opcode_alu64_imm op = ALU64_IMM_ILLEGAL),
          7   <> (Z.of_nat op) /\
          23  <> (Z.of_nat op) /\
          39  <> (Z.of_nat op) /\
          55  <> (Z.of_nat op) /\
          71  <> (Z.of_nat op) /\
          87  <> (Z.of_nat op) /\
          103 <> (Z.of_nat op) /\
          119 <> (Z.of_nat op) /\
          135 <> (Z.of_nat op) /\
          151 <> (Z.of_nat op) /\
          167 <> (Z.of_nat op) /\
          183 <> (Z.of_nat op) /\
          199 <> (Z.of_nat op).
Proof.
  intros.
  rewrite byte_to_opcode_alu64_imm_if_same in Halu; auto.
  unfold opcode_alu64_imm_if in Halu.
  change 7   with (Z.of_nat 7%nat).
  change 23  with (Z.of_nat 23%nat).
  change 39  with (Z.of_nat 39%nat).
  change 55  with (Z.of_nat 55%nat).
  change 71  with (Z.of_nat 71%nat).
  change 87  with (Z.of_nat 87%nat).
  change 103 with (Z.of_nat 103%nat).
  change 119 with (Z.of_nat 119%nat).
  change 135 with (Z.of_nat 135%nat).
  change 151 with (Z.of_nat 151%nat).
  change 167 with (Z.of_nat 167%nat).
  change 183 with (Z.of_nat 183%nat).
  change 199 with (Z.of_nat 199%nat).

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

Section Bpf_verifier_opcode_alu64_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_alu64_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_alu64_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (opcode_correct x))
     (dcons (fun x => StateLess _ (int64_correct x))
      (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_opcode_alu64_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_alu64_imm.
    simpl. (*
    unfold nat_to_opcode_alu64_reg. *)
    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD32 => bindM (upd_reg ... *)
    unfold INV.
    destruct nat_to_opcode_alu64_imm eqn: Halu. (**r case discussion on each alu64_instruction *)
    - (**r ADD64_IMM *)
      eapply correct_statement_switch with (n:= 7).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 7%nat). {
          clear - Halu.
          do 7 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 192 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 7) with 7 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r SUB64_IMM *)
      eapply correct_statement_switch with (n:= 23).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 23%nat). {
          clear - Halu.
          do 23 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 176 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 23) with 23 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MUL64_IMM *)
      eapply correct_statement_switch with (n:= 39).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 39%nat). {
          clear - Halu.
          do 39 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 160 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 39) with 39 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r DIV64_IMM *)
      eapply correct_statement_switch with (n:= 55).
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
        unfold eval_inv, correct_is_not_div_by_zero64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 55%nat). {
          clear - Halu.
          do 55 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 144 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 55) with 55 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r OR64_IMM *)
      eapply correct_statement_switch with (n:= 71).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 71%nat). {
          clear - Halu.
          do 71 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 128 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 71) with 71 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r AND64_IMM *)
      eapply correct_statement_switch with (n:= 87).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 87%nat). {
          clear - Halu.
          do 87 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 112 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 87) with 87 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LSH64_IMM *)
      eapply correct_statement_switch with (n:= 103).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _ins.
        exists (v:: (Vint (Int.repr 64)) ::nil).
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
        unfold eval_inv, correct_is_shift_range64.match_res, bool_correct in c1.
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
      + intros Hst H; cbn in H.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 103%nat). {
          clear - Halu.
          do 103 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 96 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 103) with 103 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RSH64_IMM *)
      eapply correct_statement_switch with (n:= 119).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _ins.
        exists (v:: (Vint (Int.repr 64)) ::nil).
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
        unfold eval_inv, correct_is_shift_range64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 119%nat). {
          clear - Halu.
          do 119 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 80 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 119) with 119 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r NEG64_IMM *)
      eapply correct_statement_switch with (n:= 135).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 135%nat). {
          clear - Halu.
          do 135 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 64 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 135) with 135 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOD64_IMM *)
      eapply correct_statement_switch with (n:= 151).
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
        unfold eval_inv, correct_is_not_div_by_zero64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 151%nat). {
          clear - Halu.
          do 151 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 48 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 151) with 151 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r XOR64_IMM *)
      eapply correct_statement_switch with (n:= 167).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 167%nat). {
          clear - Halu.
          do 167 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 32 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 167) with 167 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOV64_IMM *)
      eapply correct_statement_switch with (n:= 183).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 183%nat). {
          clear - Halu.
          do 183 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 183) with 183 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ARSH64_IMM *)
      eapply correct_statement_switch with (n:= 199).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _ins.
        exists (v:: (Vint (Int.repr 64)) ::nil).
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
        unfold eval_inv, correct_is_shift_range64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 199%nat). {
          clear - Halu.
          do 199 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 199) with 199 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ALU64_IMM_ILLEGAL *)
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
        apply bpf_verifier_opcode_alu64_imm_match in Halu; auto.
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

End Bpf_verifier_opcode_alu64_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_alu64_imm.
