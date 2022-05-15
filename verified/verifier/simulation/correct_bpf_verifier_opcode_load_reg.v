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
From bpf.verifier.simulation Require Import correct_is_well_src correct_is_not_div_by_zero correct_is_shift_range.


(**
Check bpf_verifier_opcode_load_reg.
bpf_verifier_opcode_load_reg
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Definition opcode_load_reg_if (op: nat) : opcode_load_reg :=
  if Nat.eqb op 97%nat then LDXW
  else if Nat.eqb op 105%nat then LDXH
  else if Nat.eqb op 113%nat then LDXB
  else if Nat.eqb op 121%nat then LDXDW
  else LDX_REG_ILLEGAL_INS.

Lemma opcode_load_reg_eqb_eq : forall a b,
    opcode_load_reg_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_load_reg :
  forall (E: nat -> opcode_load_reg)
         (F: nat -> opcode_load_reg) n,
    ((fun n => opcode_load_reg_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_load_reg_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_load_reg_if_same:
  forall (op: nat),
    (op <= 255)%nat ->
    nat_to_opcode_load_reg op = opcode_load_reg_if op.
Proof.
  intros.
  unfold nat_to_opcode_load_reg, opcode_load_reg_if.
  apply opcode_load_reg_eqb_eq.
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

Lemma bpf_verifier_opcode_load_reg_match:
  forall op
    (Hop: (op <= 255)%nat)
    (Halu : nat_to_opcode_load_reg op = LDX_REG_ILLEGAL_INS),
      97  <> (Z.of_nat op) /\
      105 <> (Z.of_nat op) /\
      113 <> (Z.of_nat op) /\
      121 <> (Z.of_nat op).
Proof.
  intros.
  rewrite byte_to_opcode_load_reg_if_same in Halu; auto.
  unfold opcode_load_reg_if in Halu.
  change 97  with (Z.of_nat 97%nat).
  change 105 with (Z.of_nat 105%nat).
  change 113 with (Z.of_nat 113%nat).
  change 121 with (Z.of_nat 121%nat).

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

Section Bpf_verifier_opcode_load_reg.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_load_reg.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_load_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (opcode_correct x))
     (dcons (fun x => StateLess _ (int64_correct x))
      (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_opcode_load_reg : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_load_reg.
    simpl.
    unfold INV.
    destruct nat_to_opcode_load_reg eqn: Hload. (**r case discussion on each load_instruction *)
    - (**r LDXW *)
      eapply correct_statement_switch with (n:= 97).
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
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_load_reg in Hload.
        assert (Hc_eq: c = 97%nat). {
          clear - Hload.
          do 97 (destruct c; [inversion Hload|]).
          destruct c; [reflexivity|].
          do 24 (destruct c; [inversion Hload|]).
          inversion Hload.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 97) with 97 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LDXH *)
      eapply correct_statement_switch with (n:= 105).
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
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_load_reg in Hload.
        assert (Hc_eq: c = 105%nat). {
          clear - Hload.
          do 105 (destruct c; [inversion Hload|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Hload|]).
          inversion Hload.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 105) with 105 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LDXB *)
      eapply correct_statement_switch with (n:= 113).
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
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_load_reg in Hload.
        assert (Hc_eq: c = 113%nat). {
          clear - Hload.
          do 113 (destruct c; [inversion Hload|]).
          destruct c; [reflexivity|].
          do 8 (destruct c; [inversion Hload|]).
          inversion Hload.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 113) with 113 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LDXDW *)
      eapply correct_statement_switch with (n:= 121).
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
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_load_reg in Hload.
        assert (Hc_eq: c = 121%nat). {
          clear - Hload.
          do 121 (destruct c; [inversion Hload|]).
          destruct c; [reflexivity|].
          inversion Hload.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 121) with 121 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LDX_REG_ILLEGAL_INS *)
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
        apply bpf_verifier_opcode_load_reg_match in Hload; auto.
        destruct Hload as (Hfirst & Hload). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Hload; rewrite Hload; clear Hload.
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

End Bpf_verifier_opcode_load_reg.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_load_reg.
