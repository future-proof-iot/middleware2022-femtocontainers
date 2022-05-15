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
Check bpf_verifier_opcode_load_imm.
bpf_verifier_opcode_load_imm
     : nat -> int64 -> M state.state bool
*)
Open Scope Z_scope.

Section Bpf_verifier_opcode_load_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_load_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_load_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (opcode_correct x))
      (dcons (fun x => StateLess _ (int64_correct x))
        (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_opcode_load_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_load_imm.
    simpl.
    unfold INV.
    destruct nat_to_opcode_load_imm eqn: Hload.
    - (**r LDDW_low *)
      eapply correct_statement_switch with (n:= 24).
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
        unfold nat_to_opcode_load_imm in Hload.
        assert (Hc_eq: c = 24%nat). {
          clear - Hload.
          do 24 (destruct c; [inversion Hload|]).
          destruct c; [reflexivity|].
          inversion Hload.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 24) with 24 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LDDW_high *)
      eapply correct_statement_switch with (n:= 16).
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
        unfold nat_to_opcode_load_imm in Hload.
        assert (Hc_eq: c = 16%nat). {
          clear - Hload.
          do 16 (destruct c; [inversion Hload|]).
          destruct c; [reflexivity|].
          do 8 (destruct c; [inversion Hload|]).
          inversion Hload.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 16) with 16 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JMP_IMM_ILLEGAL_INS *)
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
        unfold nat_to_opcode_load_imm in Hload.
        assert (Hneq: 16 <> (Z.of_nat c) /\ 24 <> (Z.of_nat c)). {
          clear - Hload.
          do 25 (destruct c; [inversion Hload; split_conj | ]).
          change 16 with (Z.of_nat 16%nat).
          change 24  with (Z.of_nat 24%nat).
          split; intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
        }
        destruct Hneq as (Hfirst & Hneq). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Hneq; rewrite Hneq; clear Hneq.
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

End Bpf_verifier_opcode_load_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_load_imm.
