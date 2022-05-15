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
Check bpf_verifier_opcode_store_reg.
bpf_verifier_opcode_store_reg
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Definition opcode_store_reg_if (op: nat) : opcode_store_reg :=
  if Nat.eqb op 99%nat then STXW
  else if Nat.eqb op 107%nat then STXH
  else if Nat.eqb op 115%nat then STXB
  else if Nat.eqb op 123%nat then STXDW
  else STX_ILLEGAL_INS.

Lemma opcode_store_reg_eqb_eq : forall a b,
    opcode_store_reg_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_store_reg :
  forall (E: nat -> opcode_store_reg)
         (F: nat -> opcode_store_reg) n,
    ((fun n => opcode_store_reg_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_store_reg_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_store_reg_if_same:
  forall (op: nat),
    (op <= 255)%nat ->
    nat_to_opcode_store_reg op = opcode_store_reg_if op.
Proof.
  intros.
  unfold nat_to_opcode_store_reg, opcode_store_reg_if.
  apply opcode_store_reg_eqb_eq.
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

Lemma bpf_verifier_opcode_store_reg_match:
  forall op
    (Hop: (op <= 255)%nat)
    (Halu : nat_to_opcode_store_reg op = STX_ILLEGAL_INS),
      99  <> (Z.of_nat op) /\
      107 <> (Z.of_nat op) /\
      115 <> (Z.of_nat op) /\
      123 <> (Z.of_nat op).
Proof.
  intros.
  rewrite byte_to_opcode_store_reg_if_same in Halu; auto.
  unfold opcode_store_reg_if in Halu.
  change 99  with (Z.of_nat 99%nat).
  change 107 with (Z.of_nat 107%nat).
  change 115 with (Z.of_nat 115%nat).
  change 123 with (Z.of_nat 123%nat).

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

Section Bpf_verifier_opcode_store_reg.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_store_reg.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_store_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (opcode_correct x))
     (dcons (fun x => StateLess _ (int64_correct x))
      (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_opcode_store_reg : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_store_reg.
    simpl.
    unfold INV.
    destruct nat_to_opcode_store_reg eqn: Hstore. (**r case discussion on each store_instruction *)
    - (**r STXW *)
      eapply correct_statement_switch with (n:= 99).
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
        unfold nat_to_opcode_store_reg in Hstore.
        assert (Hc_eq: c = 99%nat). {
          clear - Hstore.
          do 99 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 24 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 99) with 99 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STXH *)
      eapply correct_statement_switch with (n:= 107).
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
        unfold nat_to_opcode_store_reg in Hstore.
        assert (Hc_eq: c = 107%nat). {
          clear - Hstore.
          do 107 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 107) with 107 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STXB *)
      eapply correct_statement_switch with (n:= 115).
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
        unfold nat_to_opcode_store_reg in Hstore.
        assert (Hc_eq: c = 115%nat). {
          clear - Hstore.
          do 115 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 8 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 115) with 115 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STXDW *)
      eapply correct_statement_switch with (n:= 123).
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
        unfold nat_to_opcode_store_reg in Hstore.
        assert (Hc_eq: c = 123%nat). {
          clear - Hstore.
          do 123 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 123) with 123 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STX_REG_ILLEGAL_INS *)
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
        apply bpf_verifier_opcode_store_reg_match in Hstore; auto.
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

End Bpf_verifier_opcode_store_reg.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_store_reg.
