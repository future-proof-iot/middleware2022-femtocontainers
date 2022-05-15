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

From bpf.comm Require Import Regs State Monad LemmaNat rBPFMonadOp.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_opcode_mem_st_imm correct_check_mem correct_cmp_ptr32_nullM correct_upd_flag correct_store_mem_imm.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check step_opcode_mem_st_imm.
step_opcode_mem_st_imm
     : val -> val -> int -> reg -> nat -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_mem_st_imm.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (val:Type); (reg:Type); (nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := step_opcode_mem_st_imm.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_mem_st_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
  (dcons (fun _ => StateLess _ is_state_handle)
    (dcons (stateless val32_correct)
      (dcons (stateless val32_correct)
        (dcons (stateless reg_correct)
          (dcons (stateless opcode_correct)
                (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state:= fun x => StateLess _ (eq Vundef).

  Instance correct_function_step_opcode_mem_st_imm : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app, step_opcode_mem_st_imm.
    simpl.
    correct_forward.

    get_invariant _op.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    eauto.

    intros.
    destruct x eqn: HST.
    - (**r op_BPF_STW *)
      eapply correct_statement_switch with (n:= 98%Z).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 4)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        intuition reflexivity.

        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        correct_forward.
        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        correct_forward.

        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv in c2.
        rewrite Int.neg_repr.
        tauto.

        intros.
        correct_forward.
        reflexivity.

        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 4) :: v1 :: nil).
        split_and.
        unfold map_opt,exec_expr.
        rewrite p0, p1,p2.
        reflexivity.
        simpl. unfold eval_inv,correct_check_mem.match_res, stateless in *.
        intuition try congruence.
        reflexivity.
        intros.
        correct_forward.
        reflexivity.

        get_invariant _is_null.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_cmp_ptr32_nullM.match_res in c3.
        unfold match_bool in c3. subst. destruct x1;reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_get_opcode_mem_st_imm.match_res,opcode_mem_st_imm_correct  in c3.
        unfold opcode_mem_st_reg_correct in c3.
        subst. reflexivity.
      + compute ; intuition congruence.

    - (**r op_BPF_STH *)
      eapply correct_statement_switch with (n:= 106%Z).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 2)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        intuition reflexivity.

        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        correct_forward.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        correct_forward.

        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv in c2.
        rewrite Int.neg_repr.
        tauto.

        intros.
        correct_forward.
        reflexivity.

        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 2) :: v1 :: nil).
        split_and.
        unfold map_opt,exec_expr.
        rewrite p0, p1,p2.
        reflexivity.
        simpl. unfold eval_inv,correct_check_mem.match_res, stateless in *.
        intuition try congruence.
        reflexivity.
        intros.
        correct_forward.
        reflexivity.

        get_invariant _is_null.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_cmp_ptr32_nullM.match_res in c3.
        unfold match_bool in c3. subst. destruct x1;reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_get_opcode_mem_st_imm.match_res,opcode_mem_st_imm_correct  in c3.
        unfold opcode_mem_st_reg_correct in c3.
        subst. reflexivity.
      + compute ; intuition congruence.


    - (**r op_BPF_STB *)
      eapply correct_statement_switch with (n:= 114%Z).

      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 1)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        intuition reflexivity.

        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        correct_forward.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        correct_forward.

        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv in c2.
        rewrite Int.neg_repr.
        tauto.

        intros.
        correct_forward.
        reflexivity.

        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 1) :: v1 :: nil).
        split_and.
        unfold map_opt,exec_expr.
        rewrite p0, p1,p2.
        reflexivity.
        simpl. unfold eval_inv,correct_check_mem.match_res, stateless in *.
        intuition try congruence.
        reflexivity.
        intros.
        correct_forward.
        reflexivity.

        get_invariant _is_null.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_cmp_ptr32_nullM.match_res in c3.
        unfold match_bool in c3. subst. destruct x1;reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_get_opcode_mem_st_imm.match_res,opcode_mem_st_imm_correct  in c3.
        unfold opcode_mem_st_reg_correct in c3.
        subst. reflexivity.
      + compute ; intuition congruence.



    - (**r op_BPF_STDW *)
      eapply correct_statement_switch with (n:= 122%Z).

      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 8)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        intuition reflexivity.

        intros.
        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        correct_forward.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        correct_forward.

        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv in c2.
        rewrite Int.neg_repr.
        tauto.

        intros.
        correct_forward.
        reflexivity.

        correct_forward.

        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 8) :: v1 :: nil).
        split_and.
        unfold map_opt,exec_expr.
        rewrite p0, p1,p2.
        reflexivity.
        simpl. unfold eval_inv,correct_check_mem.match_res, stateless in *.
        intuition try congruence.
        reflexivity.
        intros.
        correct_forward.

        reflexivity.

        get_invariant _is_null.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_cmp_ptr32_nullM.match_res in c3.
        unfold match_bool in c3. subst. destruct x1;reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold exec_expr. rewrite p0.
        unfold eval_inv, correct_get_opcode_mem_st_imm.match_res,opcode_mem_st_imm_correct  in c3.
        unfold opcode_mem_st_reg_correct in c3.
        subst. reflexivity.
      + compute ; intuition congruence.

    - (**r op_BPF_ST_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
                   eval_inv (correct_get_opcode_mem_st_imm.match_res op_BPF_ST_ILLEGAL_INS) n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat i)) /\
          (i <> 0x62 /\ i <> 0x6a /\ i <> 0x72 /\ i <> 0x7a)%nat /\
          (i <= 255)%nat /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_st Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat i)))).
        {
          get_invariant _opcode_st.
          unfold correct_get_opcode_mem_st_imm.match_res in c2.
          exists v.
          assert (c4':=c3).
          unfold opcode_mem_st_imm_correct in c4'.
          destruct c4' as (i & V & ILL & RANGE).
          exists i.
          split ; auto.
          split ; auto.
          split ; auto.
          split ; auto.
          unfold exec_expr. congruence.
        }
        destruct Hillegal_ins as (n & i & Hprop & Hn_eq & Hill & Hrange & EX).
        exists (Z.of_nat i).
        split; auto.
        split.

        change Int.modulus with 4294967296.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        repeat destruct Coqlib.zeq; try lia.
        (* default *)
        simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        change (upd_flag Flag.BPF_ILLEGAL_INSTRUCTION) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_INSTRUCTION) (fun _ : unit => returnM tt)).
        correct_forward.

        get_invariant _st.
        exists (v ::
                (Vint (Int.neg (Int.repr 1))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split.
        reflexivity.
        intros.
        intuition reflexivity.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        intros.
        correct_forward.
        reflexivity.
Qed.

End Step_opcode_mem_st_imm.

Close Scope Z_scope.

Existing Instance correct_function_step_opcode_mem_st_imm.
