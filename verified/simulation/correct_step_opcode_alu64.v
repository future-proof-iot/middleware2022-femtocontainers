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

From bpf.comm Require Import Regs State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.
From bpf.monadicmodel Require Import Opcode.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLib CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_opcode_alu64 correct_upd_reg correct_upd_flag correct_reg64_to_reg32.

From bpf.simulation Require Import MatchState InterpreterRel.
(**
Check step_opcode_alu64.
step_opcode_alu64
     : val64_t -> val64_t -> DxRegs.reg -> int8_t -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_alu64.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (val:Type); (reg:Type); (nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := step_opcode_alu64.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_alu64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
      (dcons (stateless val64_correct)
       (dcons (stateless val64_correct)
          (dcons (stateless reg_correct)
            (dcons (stateless opcode_correct)
                    (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun _ => StateLess _ (eq Vundef).

  Lemma Cop_add : forall vl1 vl2 m,
       Cop.sem_binary_operation (globalenv p) Cop.Oadd
                                (Vlong vl1) Clightdefs.tulong (Vlong vl2) Clightdefs.tulong m =
         Some (Vlong (Int64.add vl1 vl2)).
  Proof.
    reflexivity.
  Qed.


  Instance correct_function_step_opcode_alu64 : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, step_opcode_alu64.
    simpl.
    (** goal: correct_body _ _ (bindM (get_opcode_alu64 _) ... *)
    correct_forward.

    get_invariant _op.
    exists (v::nil).
    split.
    unfold map_opt. unfold exec_expr. rewrite p0.
    reflexivity.
    intros. simpl.
    tauto.

    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD64 => bindM (upd_reg ... *)
    intros.
    unfold INV.
    destruct x eqn: Halu. (**r case discussion on each alu64_instruction *)
    - (**r op_BPF_ADD64 *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold eval_inv,stateless in *.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.add vl1 vl2) :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        unfold eval_inv. reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_SUB64 *)
      eapply correct_statement_switch with (n:= 16).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.sub vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MUL64 *)
      eapply correct_statement_switch with (n:= 32).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.mul vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_DIV64 *)
      eapply correct_statement_switch with (n:= 48).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.val64_divlu, Val.divlu. (**r star here *)
        unfold rBPFValues.compl_ne.
        correct_forward.
        (**r correct_body p unit (if rBPFValues.compl_ne c0 val64_zero then ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        rewrite Bool.negb_true_iff in Hcnd.
        rewrite Hcnd.
        exists (v ::v0 :: Vlong (Int64.divu vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        simpl.
        unfold Cop.sem_div, Cop.sem_binarith;
        simpl.
        unfold Cop.sem_cast; simpl.
        rewrite Hcnd.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        reflexivity.

        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::Vint (Int.neg (Int.repr 9)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        reflexivity.

        intros.
        get_invariant _src64.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        unfold stateless, val64_correct in c3.
        destruct c3 as (c3_0 & c3_vl & c3_1).
        subst.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. clear. intuition congruence.
    - (**r op_BPF_OR64 *)
      eapply correct_statement_switch with (n:= 64).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.or vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_AND64 *)
      eapply correct_statement_switch with (n:= 80).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.
        (**r because upd_reg return unit, here we use *_unit? *)

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.and vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_LSH64 *)
      eapply correct_statement_switch with (n:= 96).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _src64.
        unfold eval_inv,val64_correct,stateless in c3.
        destruct c3 as (Hv_eq & (vl & Hvl_eq)); subst.
        exists (Vlong vl :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        split; [reflexivity |].
        intros.
        simpl.
        unfold stateless,val64_correct.
        intuition.
        eexists ; reflexivity.
        intros.
        unfold rBPFValues.compu_lt_32.
        (**r correct_body p unit (if rBPFValues.compu_lt_32 ... *)
        correct_forward.
        correct_forward.
 simpl in H.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src32.
        unfold eval_inv in *.
        unfold stateless in c3.
        unfold is_state_handle in *.
        unfold stateless, reg_correct in c4.
        unfold stateless, val64_correct in c5.
        destruct c5 as (Hv1_eq & (vl & Hvl_eq)); subst.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c6.
        destruct c6 as (Hv2_eq & (vi & Hvi_eq)); subst.
        exists ((Vptr st_blk Ptrofs.zero) :: (Vint (Int.repr (id_of_reg c1))) :: (Val.shll (Vlong vl) (Vint vi)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        simpl.
        unfold Cop.sem_shl, Cop.sem_shift; simpl.
        change Int64.iwordsize' with (Int.repr 64).
        rewrite Hcnd.
        split.
        unfold Int64.shl', Int64.shl.
        rewrite Hint_unsigned_int64; reflexivity.
        intros.
        unfold is_state_handle. intuition.
        reflexivity.
        unfold val64_correct.
        eauto.
        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        intros.
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        reflexivity.

        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_SHIFT) fn ... *)
        correct_forward.

        simpl in H.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) :: Vint (Int.neg (Int.repr 10)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split; [reflexivity |].
        intros.
        unfold is_state_handle, stateless, flag_correct, int_of_flag.
        simpl.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        reflexivity.

        intros.
        get_invariant _src32.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c3.
        destruct c3 as (Hv_eq & vi & Hvi_eq); subst.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold eval_inv,correct_get_opcode_alu64.match_res, opcode_alu64_correct in c3.
        unfold exec_expr.
        rewrite p0. f_equal.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_RSH64 *)
      eapply correct_statement_switch with (n:= 112).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _src64.
        unfold val64_correct,stateless in c3.
        destruct c3 as (Hv_eq & (vl & Hvl_eq)); subst.
        exists (Vlong vl :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        split; [reflexivity |].
        intros.
        simpl.
        unfold stateless,val64_correct.
        intuition.
        eexists ; reflexivity.
        intros.
        (**r correct_body p unit (if rBPFValues.compu_lt_32 ... *)
        unfold rBPFValues.compu_lt_32.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src32.
        unfold eval_inv,stateless, is_state_handle in c3.
        subst.
        unfold eval_inv,stateless, reg_correct in c4.
        unfold stateless, val64_correct in c5.
        destruct c5 as (Hv1_eq & (vl & Hvl_eq)); subst.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c6.
        destruct c6 as (Hv2_eq & (vi & Hvi_eq)); subst.
        exists ((Vptr st_blk Ptrofs.zero) :: (Vint (Int.repr (id_of_reg c1))) :: (Val.shrlu (Vlong vl) (Vint vi)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        simpl.
        unfold Cop.sem_shr, Cop.sem_shift; simpl.
        change Int64.iwordsize' with (Int.repr 64).
        rewrite Hcnd.
        split.
        unfold Int64.shru', Int64.shru.
        rewrite Hint_unsigned_int64. reflexivity.
        intros.
        split_and;auto; try reflexivity.
        unfold val64_correct;eauto.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        simpl. intros.
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        reflexivity.

        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_SHIFT) fn ... *)
        correct_forward.
 simpl in H.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) :: Vint (Int.neg (Int.repr 10)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, flag_correct, int_of_flag.
        simpl.
        intuition. reflexivity.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        simpl; intros.
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.

        intros.
        get_invariant _src32.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c3.
        destruct c3 as (Hv_eq & vi & Hvi_eq); subst.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold correct_get_opcode_alu64.match_res, opcode_alu64_correct in c3.
        unfold exec_expr.
        rewrite p0. f_equal.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_NEG64 *)
      eapply correct_statement_switch with (n:= 128).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v :: v0 :: Vlong (Int64.neg vl1) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        unfold Cop.sem_unary_operation; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::Vint (Int.neg (Int.repr 1)) :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.

        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c3.
        destruct c3 as (Hv_eq & Hrange).
        rewrite <- Hv_eq.
        destruct (c2 =? 135)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c2)) (Int.repr 135) = false). {
          apply Int.eq_false.
          apply nat8_neq_k; auto; lia.
        }
        rewrite Hneq; clear Hneq.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 135 240))) with (Int.repr 128) in c3.
        assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MOD64 *)
      eapply correct_statement_switch with (n:= 144).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_ne, val64_zero.
        (**r correct_body p unit (if rBPFValues.compl_ne c0 val64_zero then ... *)
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        unfold rBPFValues.val64_modlu, Val.modlu. (**r star here *)
        rewrite Bool.negb_true_iff in Hcnd.
        rewrite Hcnd.
        exists (v ::v0 :: Vlong (Int64.modu vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        simpl.
        unfold Cop.sem_mod, Cop.sem_binarith;
        simpl.
        unfold Cop.sem_cast; simpl.
        rewrite Hcnd.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.

        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::Vint (Int.neg (Int.repr 9)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.

        intros.
        get_invariant _src64.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        unfold stateless, val64_correct in c3.
        destruct c3 as (c3_0 & c3_vl & c3_1).
        subst.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_XOR64 *)
      eapply correct_statement_switch with (n:= 160).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.xor vl1 vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MOV64 *)
      eapply correct_statement_switch with (n:= 176).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src64.
        unfold val64_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (vl2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p3.
        split.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val64_correct.
        split; auto. eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu64.match_res in c3.
        unfold opcode_alu64_correct in c3.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        change (Int.repr (Z.of_nat (Nat.land 183 240))) with (Int.repr 176) in c3.
        change (Int.repr (Z.of_nat (Nat.land 191 240))) with (Int.repr 176) in c3.
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_ARSH64 *)
      eapply correct_statement_switch with (n:= 192).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _src64.
        unfold val64_correct,stateless in c3.
        destruct c3 as (Hv_eq & (vl & Hvl_eq)); subst.
        exists (Vlong vl :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        split; [reflexivity |].
        intros.
        simpl.
        unfold stateless,val64_correct.
        intuition.
        eexists ; reflexivity.
        intros.
        unfold rBPFValues.compu_lt_32.
        (**r correct_body p unit (if rBPFValues.compu_lt_32 ... *)
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst64.
        get_invariant _src32.
        unfold eval_inv, is_state_handle in c3.
        subst.
        unfold eval_inv,stateless, reg_correct in c4.
        unfold eval_inv,stateless, val64_correct in c5.
        destruct c5 as (Hv1_eq & (vl & Hvl_eq)); subst.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c6.
        destruct c6 as (Hv2_eq & (vi & Hvi_eq)); subst.
        exists ((Vptr st_blk Ptrofs.zero) :: (Vint (Int.repr (id_of_reg c1))) :: (Val.shrl (Vlong vl) (Vint vi)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        simpl.
        unfold Cop.sem_shr, Cop.sem_shift; simpl.
        change Int64.iwordsize' with (Int.repr 64).
        rewrite Hcnd.
        unfold Cop.sem_cast; simpl.
        split.
        unfold Int64.shr', Int64.shr.
        rewrite Hint_unsigned_int64; reflexivity.
        intros.
        unfold stateless, reg_correct, val64_correct.
        simpl.
        intuition.
        reflexivity.
        eexists ; reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        reflexivity.
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_SHIFT) fn ... *)
        correct_forward.

        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) :: Vint (Int.neg (Int.repr 10)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, flag_correct, int_of_flag.
        simpl.
        intuition.
        reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros. reflexivity.

        get_invariant _src32.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c3.
        destruct c3 as (Hv_eq & vi & Hvi_eq); subst.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu64.
        unfold correct_get_opcode_alu64.match_res, opcode_alu64_correct in c3.
        unfold exec_expr.
        rewrite p0. f_equal.
        (* opcode_alu64_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_ALU64_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
                   eval_inv (correct_get_opcode_alu64.match_res op_BPF_ALU64_ILLEGAL_INS) n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\
          is_illegal_alu64_ins i /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_alu64 Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat (Nat.land i 240))))).
        {
          get_invariant _opcode_alu64.
          unfold eval_inv,correct_get_opcode_alu64.match_res in c3.
          exists v.
          assert (c3':=c3).
          unfold opcode_alu64_correct in c3'.
          destruct c3' as (i & V & ILL).
          exists i.
          split ; auto.
          split ; auto.
          split ; auto.
          unfold exec_expr. congruence.
        }
        destruct Hillegal_ins as (n & i & Hprop & Hn_eq & Hill & EX).
        exists (Z.of_nat (Nat.land i 240)).
        split; auto.
        split.

        change Int.modulus with 4294967296.
        assert (Hand_le: (Nat.land 240 i <= 240)%nat). {
          apply LemmaNat.land_bound.
        }
        rewrite Nat.land_comm.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        unfold is_illegal_alu64_ins in Hill.
        repeat match goal with
        | |- context[Coqlib.zeq ?x (Z.of_nat (Nat.land i 240))] =>
            destruct (Coqlib.zeq x (Z.of_nat (Nat.land i 240))) ; try lia
        end.
        (* default *)
        simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) ::
                (Vint (Int.neg (Int.repr 1))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split.
        reflexivity.
        intros.
        unfold stateless, flag_correct, int_of_flag; simpl.
        split; auto.
        reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        reflexivity.
Qed.

End Step_opcode_alu64.

Close Scope Z_scope.

Existing Instance correct_function_step_opcode_alu64.
