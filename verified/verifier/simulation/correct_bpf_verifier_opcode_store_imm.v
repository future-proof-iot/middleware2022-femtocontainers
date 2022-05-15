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


(**
Check bpf_verifier_opcode_store_imm.
bpf_verifier_opcode_store_imm
     : nat -> int64 -> M state.state bool
*)
Open Scope Z_scope.

Definition opcode_store_imm_if (op: nat) : opcode_store_imm :=
  if Nat.eqb op 98%nat then STW
  else if Nat.eqb op 106%nat then STH
  else if Nat.eqb op 114%nat then STB
  else if Nat.eqb op 122%nat then STDW
  else ST_ILLEGAL_INS.

Lemma opcode_store_imm_eqb_eq : forall a b,
    opcode_store_imm_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl; congruence.
Qed.

Lemma lift_opcode_store_imm :
  forall (E: nat -> opcode_store_imm)
         (F: nat -> opcode_store_imm) n,
    ((fun n => opcode_store_imm_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_store_imm_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_store_imm_if_same:
  forall (op: nat),
    (op <= 255)%nat ->
    nat_to_opcode_store_imm op = opcode_store_imm_if op.
Proof.
  intros.
  unfold nat_to_opcode_store_imm, opcode_store_imm_if.
  apply opcode_store_imm_eqb_eq.
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

Lemma bpf_verifier_opcode_store_imm_match:
  forall op
    (Hop: (op <= 255)%nat)
    (Halu : nat_to_opcode_store_imm op = ST_ILLEGAL_INS),
      98  <> (Z.of_nat op) /\
      106 <> (Z.of_nat op) /\
      114 <> (Z.of_nat op) /\
      122 <> (Z.of_nat op).
Proof.
  intros.
  rewrite byte_to_opcode_store_imm_if_same in Halu; auto.
  unfold opcode_store_imm_if in Halu.
  change 98  with (Z.of_nat 98%nat).
  change 106 with (Z.of_nat 106%nat).
  change 114 with (Z.of_nat 114%nat).
  change 122 with (Z.of_nat 122%nat).

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


Section Bpf_verifier_opcode_store_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_store_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_store_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (opcode_correct x))
      (dcons (fun x => StateLess _ (int64_correct x))
        (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_opcode_store_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_store_imm.
    simpl.
    unfold INV.
    destruct nat_to_opcode_store_imm eqn: Hstore.
    - (**r STW *)
      eapply correct_statement_switch with (n:= 98).
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
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 98%nat). {
          clear - Hstore.
          do 98 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 24 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 98) with 98 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STH *)
      eapply correct_statement_switch with (n:= 106).
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
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 106%nat). {
          clear - Hstore.
          do 106 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 106) with 106 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STB *)
      eapply correct_statement_switch with (n:= 114).
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
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 114%nat). {
          clear - Hstore.
          do 114 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 8 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 114) with 114 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STDW *)
      eapply correct_statement_switch with (n:= 122).
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
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 122%nat). {
          clear - Hstore.
          do 122 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 122) with 122 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ST_ILLEGAL_INS *)
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
        rewrite <- c1.
        reflexivity.
        split.

        change Int.modulus with 4294967296.
        change Int.max_unsigned with 4294967295 in Hc1_range.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        apply bpf_verifier_opcode_store_imm_match in Hstore; auto.
        destruct Hstore as (Hfirst & Hstore). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Hstore; rewrite Hstore; clear Hstore.
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

End Bpf_verifier_opcode_store_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_store_imm.
