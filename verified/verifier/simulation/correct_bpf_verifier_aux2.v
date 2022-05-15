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
From bpf.verifier.simulation Require Import correct_bpf_verifier_opcode_alu64_imm  correct_bpf_verifier_opcode_alu64_reg correct_bpf_verifier_opcode_alu32_imm correct_bpf_verifier_opcode_alu32_reg correct_bpf_verifier_opcode_branch_imm correct_bpf_verifier_opcode_branch_reg correct_bpf_verifier_opcode_load_imm correct_bpf_verifier_opcode_load_reg correct_bpf_verifier_opcode_store_imm correct_bpf_verifier_opcode_store_reg.


(**
Check bpf_verifier_aux2.
bpf_verifier_aux2
     : nat -> nat -> nat -> int64 -> M state.state bool

*)
Open Scope Z_scope.
Lemma bpf_verifier_aux2_match:
  forall c
    (Hopcode : match Nat.land c 7 with
      | 0%nat => LD_IMM
      | 1%nat => LD_REG
      | 2%nat => ST_IMM
      | 3%nat => ST_REG
      | 4%nat => ALU32
      | 5%nat => Branch
      | 7%nat => ALU64
      | _ => ILLEGAL
      end = ILLEGAL),
        7 <> (Z.land (Z.of_nat c) 7) /\
        4 <> (Z.land (Z.of_nat c) 7) /\
        5 <> (Z.land (Z.of_nat c) 7) /\
        0 <> (Z.land (Z.of_nat c) 7) /\
        1 <> (Z.land (Z.of_nat c) 7) /\
        2 <> (Z.land (Z.of_nat c) 7) /\
        3 <> (Z.land (Z.of_nat c) 7).
Proof. 
  intros.
  change 0 with (Z.of_nat 0%nat).
  change 1 with (Z.of_nat 1%nat).
  change 2 with (Z.of_nat 2%nat).
  change 3 with (Z.of_nat 3%nat).
  change 4 with (Z.of_nat 4%nat).
  change 5 with (Z.of_nat 5%nat).
  change 7 with (Z.of_nat 7%nat).
  rewrite land_land.
  remember (Nat.land c 7) as n.
  do 8 (destruct n; [inversion Hopcode; split_conj | ]).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.



Section Bpf_verifier_aux2.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (nat:Type); (nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_aux2.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_aux2.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (nat_correct x))
      (dcons (fun x => StateLess _ (nat_correct x))
        (dcons (fun x => StateLess _ (opcode_correct x))
          (dcons (fun x => StateLess _ (int64_correct x))
            (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier_aux2 : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_aux2.
    simpl.
    unfold INV.
    destruct nat_to_opcode eqn: Hopcode.
    - (**r ALU64 *)
      eapply correct_statement_switch with (n:= 7).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        * correct_forward.

          get_invariant _op.
          get_invariant _ins.
          exists (v::v0::nil).
          split.
          unfold map_opt, exec_expr. rewrite p0, p1.
          reflexivity.
          intros; simpl.
          unfold eval_inv in *.
          intuition congruence.
          intros.

          correct_forward.
          get_invariant _b.
          exists v.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, match_res.
          unfold eval_inv, correct_bpf_verifier_opcode_alu64_imm.match_res in c3.
          split; [reflexivity|].
          split; [assumption|].
          unfold bool_correct in c3.
          rewrite c3.
          split. unfold Cop.sem_cast; simpl.
          destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x; reflexivity.
        * correct_forward.

          get_invariant _op.
          get_invariant _ins.
          exists (v::v0::nil).
          split.
          unfold map_opt, exec_expr. rewrite p0, p1.
          reflexivity.
          intros; simpl.
          unfold eval_inv in *.
          intuition congruence.
          intros.

          correct_forward.
          get_invariant _b.
          exists v.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, match_res.
          unfold eval_inv, correct_bpf_verifier_opcode_alu64_imm.match_res in c3.
          split; [reflexivity|].
          split; [assumption|].
          unfold bool_correct in c3.
          rewrite c3.
          split. unfold Cop.sem_cast; simpl.
          destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x; reflexivity.
        * intros.
          get_invariant _op.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, opcode_correct in c3.
          destruct c3 as (Hc3_eq & Hc3_range).
          rewrite <- Hc3_eq.
          simpl.
          unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
          fold Int.zero.
          f_equal.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (Hc3_eq & Hc3_range).
        rewrite <- Hc3_eq.
        simpl.
        unfold Cop.sem_cast; simpl.
        unfold nat_to_opcode in Hopcode.
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with (Z.of_nat 7%nat).
        rewrite Int.unsigned_repr.
        rewrite land_land.
        remember (Nat.land c1 7) as n.
        assert (Hc1_and: n = 7%nat). {
          clear - Hopcode.
          do 8 (destruct n; [try inversion Hopcode; reflexivity | ]).
          inversion Hopcode.
        }
        rewrite Hc1_and.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
      + compute. intuition congruence.
    - (**r ALU32 *)
      eapply correct_statement_switch with (n:= 4).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        * correct_forward.

          get_invariant _op.
          get_invariant _ins.
          exists (v::v0::nil).
          split.
          unfold map_opt, exec_expr. rewrite p0, p1.
          reflexivity.
          intros; simpl.
          unfold eval_inv in *.
          intuition congruence.
          intros.

          correct_forward.
          get_invariant _b.
          exists v.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, match_res.
          unfold eval_inv, correct_bpf_verifier_opcode_alu32_imm.match_res in c3.
          split; [reflexivity|].
          split; [assumption|].
          unfold bool_correct in c3.
          rewrite c3.
          split. unfold Cop.sem_cast; simpl.
          destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x; reflexivity.
        * correct_forward.

          get_invariant _op.
          get_invariant _ins.
          exists (v::v0::nil).
          split.
          unfold map_opt, exec_expr. rewrite p0, p1.
          reflexivity.
          intros; simpl.
          unfold eval_inv in *.
          intuition congruence.
          intros.

          correct_forward.
          get_invariant _b.
          exists v.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, match_res.
          unfold eval_inv, correct_bpf_verifier_opcode_alu32_imm.match_res in c3.
          split; [reflexivity|].
          split; [assumption|].
          unfold bool_correct in c3.
          rewrite c3.
          split. unfold Cop.sem_cast; simpl.
          destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x; reflexivity.
        * intros.
          get_invariant _op.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, opcode_correct in c3.
          destruct c3 as (Hc3_eq & Hc3_range).
          rewrite <- Hc3_eq.
          simpl.
          unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
          fold Int.zero.
          f_equal.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (Hc3_eq & Hc3_range).
        rewrite <- Hc3_eq.
        simpl.
        unfold Cop.sem_cast; simpl.
        unfold nat_to_opcode in Hopcode.
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with (Z.of_nat 7%nat).
        rewrite Int.unsigned_repr.
        rewrite land_land.
        remember (Nat.land c1 7) as n.
        assert (Hc1_and: n = 4%nat). {
          clear - Hopcode.
          do 8 (destruct n; [try inversion Hopcode; reflexivity | ]).
          inversion Hopcode.
        }
        rewrite Hc1_and.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
      + compute. intuition congruence.
    - (**r Branch *)
      eapply correct_statement_switch with (n:= 5).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.
        * correct_forward.

          get_invariant _pc.
          get_invariant _len.
          get_invariant _op.
          get_invariant _ins.
          exists (v::v0::v1::v2::nil).
          split.
          unfold map_opt, exec_expr. rewrite p0, p1, p2, p3.
          reflexivity.
          intros; simpl.
          unfold eval_inv in *.
          intuition congruence.
          intros.

          correct_forward.
          get_invariant _b.
          exists v.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, match_res.
          unfold eval_inv, correct_bpf_verifier_opcode_branch_imm.match_res in c3.
          split; [reflexivity|].
          split; [assumption|].
          unfold bool_correct in c3.
          rewrite c3.
          split. unfold Cop.sem_cast; simpl.
          destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x; reflexivity.
        * correct_forward.

          get_invariant _pc.
          get_invariant _len.
          get_invariant _op.
          get_invariant _ins.
          exists (v::v0::v1::v2::nil).
          split.
          unfold map_opt, exec_expr. rewrite p0, p1, p2, p3.
          reflexivity.
          intros; simpl.
          unfold eval_inv in *.
          intuition congruence.
          intros.

          correct_forward.
          get_invariant _b.
          exists v.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, match_res.
          unfold eval_inv, correct_bpf_verifier_opcode_branch_imm.match_res in c3.
          split; [reflexivity|].
          split; [assumption|].
          unfold bool_correct in c3.
          rewrite c3.
          split. unfold Cop.sem_cast; simpl.
          destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x; reflexivity.
        * intros.
          get_invariant _op.
          unfold exec_expr.
          rewrite p0.
          unfold eval_inv, opcode_correct in c3.
          destruct c3 as (Hc3_eq & Hc3_range).
          rewrite <- Hc3_eq.
          simpl.
          unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
          fold Int.zero.
          f_equal.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (Hc3_eq & Hc3_range).
        rewrite <- Hc3_eq.
        simpl.
        unfold Cop.sem_cast; simpl.
        unfold nat_to_opcode in Hopcode.
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with (Z.of_nat 7%nat).
        rewrite Int.unsigned_repr.
        rewrite land_land.
        remember (Nat.land c1 7) as n.
        assert (Hc1_and: n = 5%nat). {
          clear - Hopcode.
          do 8 (destruct n; [try inversion Hopcode; reflexivity | ]).
          inversion Hopcode.
        }
        rewrite Hc1_and.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
      + compute. intuition congruence.
    - (**r LD_IMM *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_bpf_verifier_opcode_load_imm.match_res in c3.
        split; [reflexivity|].
        split; [assumption|].
        unfold bool_correct in c3.
        rewrite c3.
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (Hc3_eq & Hc3_range).
        rewrite <- Hc3_eq.
        simpl.
        unfold Cop.sem_cast; simpl.
        unfold nat_to_opcode in Hopcode.
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with (Z.of_nat 7%nat).
        rewrite Int.unsigned_repr.
        rewrite land_land.
        remember (Nat.land c1 7) as n.
        assert (Hc1_and: n = 0%nat). {
          clear - Hopcode.
          do 8 (destruct n; [try inversion Hopcode; reflexivity | ]).
          inversion Hopcode.
        }
        rewrite Hc1_and.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
      + compute. intuition congruence.
    - (**r LD_REG *)
      eapply correct_statement_switch with (n:= 1).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_bpf_verifier_opcode_load_reg.match_res in c3.
        split; [reflexivity|].
        split; [assumption|].
        unfold bool_correct in c3.
        rewrite c3.
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (Hc3_eq & Hc3_range).
        rewrite <- Hc3_eq.
        simpl.
        unfold Cop.sem_cast; simpl.
        unfold nat_to_opcode in Hopcode.
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with (Z.of_nat 7%nat).
        rewrite Int.unsigned_repr.
        rewrite land_land.
        remember (Nat.land c1 7) as n.
        assert (Hc1_and: n = 1%nat). {
          clear - Hopcode.
          do 8 (destruct n; [try inversion Hopcode; reflexivity | ]).
          inversion Hopcode.
        }
        rewrite Hc1_and.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
      + compute. intuition congruence.
    - (**r ST_IMM *)
      eapply correct_statement_switch with (n:= 2).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_bpf_verifier_opcode_store_imm.match_res in c3.
        split; [reflexivity|].
        split; [assumption|].
        unfold bool_correct in c3.
        rewrite c3.
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (Hc3_eq & Hc3_range).
        rewrite <- Hc3_eq.
        simpl.
        unfold Cop.sem_cast; simpl.
        unfold nat_to_opcode in Hopcode.
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with (Z.of_nat 7%nat).
        rewrite Int.unsigned_repr.
        rewrite land_land.
        remember (Nat.land c1 7) as n.
        assert (Hc1_and: n = 2%nat). {
          clear - Hopcode.
          do 8 (destruct n; [try inversion Hopcode; reflexivity | ]).
          inversion Hopcode.
        }
        rewrite Hc1_and.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
      + compute. intuition congruence.
    - (**r ST_REG *)
      eapply correct_statement_switch with (n:= 3).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        intuition congruence.
        intros.

        correct_forward.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_bpf_verifier_opcode_store_reg.match_res in c3.
        split; [reflexivity|].
        split; [assumption|].
        unfold bool_correct in c3.
        rewrite c3.
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (Hc3_eq & Hc3_range).
        rewrite <- Hc3_eq.
        simpl.
        unfold Cop.sem_cast; simpl.
        unfold nat_to_opcode in Hopcode.
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with (Z.of_nat 7%nat).
        rewrite Int.unsigned_repr.
        rewrite land_land.
        remember (Nat.land c1 7) as n.
        assert (Hc1_and: n = 3%nat). {
          clear - Hopcode.
          do 8 (destruct n; [try inversion Hopcode; reflexivity | ]).
          inversion Hopcode.
        }
        rewrite Hc1_and.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
      + compute. intuition congruence.
    - (**r ILLEGAL *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (c3 & Hc3_range).
        exists (Z.land (Z.of_nat c1) 7).
        split.
        unfold exec_expr.
        rewrite p0.
        rewrite <- c3.
        unfold Cop.sem_binary_operation, Cop.sem_cast; simpl.
        rewrite Int.zero_ext_and.
        rewrite Int.and_assoc.
        change (two_p 8 - 1) with 255.
        change (Int.and (Int.repr 7) (Int.repr 255)) with (Int.repr 7).
        unfold Int.and.
        change (Int.unsigned (Int.repr 7)) with 7.
        rewrite Int.unsigned_repr.
        reflexivity.
        change Int.max_unsigned with 4294967295.
        lia.
        lia.
        split.

        change Int.modulus with 4294967296.
        change 7 with (Z.of_nat 7%nat).
        rewrite land_land.
        assert (Hland7: (Nat.land 7 c1 <= 7)%nat) by apply land_bound.
        rewrite Nat.land_comm.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        unfold nat_to_opcode in Hopcode.
        apply bpf_verifier_aux2_match in Hopcode.
        destruct Hopcode as (Hfirst & Hopcode). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Hopcode; rewrite Hopcode; clear Hopcode.
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

End Bpf_verifier_aux2.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_aux2.
