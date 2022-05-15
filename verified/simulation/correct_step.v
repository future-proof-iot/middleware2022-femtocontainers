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

From bpf.simulation Require Import correct_eval_pc correct_eval_ins correct_get_opcode_ins correct_get_opcode correct_get_dst correct_eval_reg correct_get_src64 correct_step_opcode_alu64 correct_reg64_to_reg32 correct_get_src32 correct_step_opcode_alu32 correct_get_offset correct_step_opcode_branch correct_get_immediate correct_step_opcode_mem_ld_imm correct_get_addr_ofs correct_step_opcode_mem_ld_reg correct_step_opcode_mem_st_imm correct_step_opcode_mem_st_reg correct_upd_flag.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check rBPFInterpreter.step.
rBPFInterpreter.step
     : M unit

*)
Open Scope Z_scope.

Section Step.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := rBPFInterpreter.step.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x => StateLess _ (eq Vundef).


  Instance correct_function_step: forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, rBPFInterpreter.step.
    simpl.
    (** goal: correct_body _ _ (bindM (eval_pc _) ... *)
    correct_forward.

    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    eauto.

    intros.
    (** goal: correct_body _ _ (bindM (eval_ins _) ... *)
    correct_forward.

    get_invariant _st.
    get_invariant _pc.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
    intros; simpl.
    eauto.

    intros.
    (** goal: correct_body _ _ (bindM (get_opcode_ins _) ... *)
    correct_forward.

    get_invariant _ins.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    eauto.

    intros.
    (** goal: correct_body _ _ (bindM (get_opcode _) ... *)
    correct_forward.

    get_invariant _op.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    eauto.

    intros.
    (** goal: correct_body _ _ (bindM (get_dst _) ... *)
    correct_forward.

    get_invariant _ins.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    eauto.

    intros.
    (** goal: correct_body _ _
              match x with
              | op_BPF_ALU64 => bindM (eval_reg ... *)
    unfold INV.
    destruct x2 eqn: Hins.
    - (**r op_BPF_ALU64 *)
      eapply correct_statement_switch with (n:= 7).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (**r because upd_reg return unit, here we use *_unit? *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src64 _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1,p2; reflexivity.
        intros; simpl.
        eauto.
        intros.

        assert (Heq:
              step_opcode_alu64 x4 x5 x3 x1 =
              bindM (step_opcode_alu64 x4 x5 x3 x1) (fun _ : unit => returnM tt)). {
          clear - st7.
        Ltac val_op :=
          match goal with
          | |- context[match
                   match ?X with
                   | _ => _
                   end
                  with _ => _ end] =>
            destruct X; try reflexivity
          end.
          unfold step_opcode_alu64, get_opcode_alu64.
          unfold bindM, returnM.
          destruct byte_to_opcode_alu64; try reflexivity; unfold upd_reg.
          val_op. val_op.  val_op.
          destruct (rBPFValues.compl_ne _ _); try reflexivity.
          destruct (rBPFValues.val64_divlu _ _); try reflexivity.
          val_op. val_op.
          unfold reg64_to_reg32, returnM.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.shll; try reflexivity.
          unfold reg64_to_reg32, returnM.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.shrlu; try reflexivity.
          destruct (x1 =? 135)%nat; try reflexivity.
          destruct Val.negl; try reflexivity.
          destruct rBPFValues.compl_ne; try reflexivity.
          destruct rBPFValues.val64_modlu; try reflexivity.
          destruct Val.xorl; try reflexivity.
          destruct x5; try reflexivity.
          unfold reg64_to_reg32, returnM.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.shrl; try reflexivity.
        }
        rewrite Heq; clear Heq.
        correct_forward.

        get_invariant _st.
        get_invariant _dst64.
        get_invariant _src64.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 :: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        intros.

        unfold eval_inv, match_res.
        reflexivity.
      + reflexivity.
      + intros. simpl in H0.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold eval_inv, opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_ALU32 *)
      eapply correct_statement_switch with (n:= 4).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (reg64_to_reg32 _) ... *)
        correct_forward.

        get_invariant _dst64.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src32 _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1,p2; reflexivity.
        intros; simpl.
        intuition eauto.

        intros.

        assert (Heq:
              step_opcode_alu32 x5 x6 x3 x1 =
              bindM (step_opcode_alu32 x5 x6 x3 x1) (fun _ : unit => returnM tt)). {
          clear - st7.
          unfold step_opcode_alu32, get_opcode_alu32.
          unfold bindM, returnM.
          destruct byte_to_opcode_alu32; try reflexivity; unfold upd_reg.
          val_op. val_op.  val_op.
          destruct rBPFValues.comp_ne_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct (x1 =? 132)%nat; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.comp_ne_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.longofint; try reflexivity.
        }
        rewrite Heq; clear Heq.
        correct_forward.

        get_invariant _st.
        get_invariant _dst32.
        get_invariant _src32.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 :: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        intros.
        unfold eval_inv.
        reflexivity.
      + reflexivity.
      + intros. simpl in H0.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold eval_inv, opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Branch *)
      eapply correct_statement_switch with (n:= 5).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src64 _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1,p2; reflexivity.
        intros; simpl.
        intuition eauto.

        intros.

        assert (Heq:
              step_opcode_branch x4 x6 x x5 x1 =
              bindM (step_opcode_branch x4 x6 x x5 x1) (fun _ : unit => returnM tt)). {
          clear - st7.
          unfold step_opcode_branch, get_opcode_branch.
          unfold bindM, returnM.
          destruct byte_to_opcode_branch; try reflexivity; unfold upd_pc.
          destruct (x1 =? 5)%nat; try reflexivity.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality.
          intros.
          match goal with
          | |- match (if ?X then _ else _) with _ => _ end = _ =>
            destruct X; try reflexivity
          end.
          Ltac simpl_funcExt := 
          match goal with
          | |- context[if ?X then _ else _] =>
            destruct X; [apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intros | reflexivity]
          end.
          all: simpl_funcExt; destruct (Int.cmpu Cle (Int.add x x5) (Int.sub (Int.repr (Z.of_nat (ins_len x0))) (Int.repr 2)))%bool; try reflexivity.
          destruct _bpf_get_call; try reflexivity.
          destruct p0.
          destruct cmp_ptr32_nullM; try reflexivity.
          destruct p0.
          destruct b; try reflexivity.
          destruct exec_function; try reflexivity.
          destruct p0.
          unfold upd_reg.
          destruct Val.longofintu; try reflexivity.

          destruct _bpf_get_call; try reflexivity.
          destruct p0.
          destruct cmp_ptr32_nullM; try reflexivity.
          destruct p0.
          destruct b; try reflexivity.
          destruct exec_function; try reflexivity.
          destruct p0.
          unfold upd_reg.
          destruct Val.longofintu; try reflexivity.
        }
        rewrite Heq; clear Heq.
        correct_forward.

        get_invariant _st.
        get_invariant _dst64.
        get_invariant _src64.
        get_invariant _pc.
        get_invariant _ofs.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 ::v4:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4, p5.
        unfold eval_inv, correct_get_offset.match_res, sint32_correct in c3.
        destruct c3 as (c3 & c3_range).
        split.
        rewrite <- c3.
        simpl.
        reflexivity.
        intros; simpl.
        intuition eauto.
        unfold uint32_correct.
        split; [assumption | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        intros.
        unfold eval_inv.
        reflexivity.
      + reflexivity.
      + intros. simpl in H0.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold eval_inv, opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_ld_imm *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_immediate _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_ld_imm x5 x4 x3 x1 =
              bindM (step_opcode_mem_ld_imm x5 x4 x3 x1) (fun _ : unit => returnM tt)). {
          clear - st6.
          unfold step_opcode_mem_ld_imm, get_opcode_mem_ld_imm.
          unfold bindM, returnM.
          destruct byte_to_opcode_mem_ld_imm; try reflexivity.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality.
          intros.
          unfold upd_reg.
          destruct Val.orl; try reflexivity.
        }
        rewrite Heq; clear Heq.
        correct_forward.

        get_invariant _st.
        get_invariant _imm.
        get_invariant _dst64.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2::v3:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        intros.
        unfold eval_inv.
        reflexivity.
      + reflexivity.
      + intros. simpl in H0.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold eval_inv, opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_ld_reg *)
      eapply correct_statement_switch with (n:= 1).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (get_src _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _src.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_addr_ofs _) ... *)
        correct_forward.

        get_invariant _src64.
        get_invariant _ofs.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_ld_reg x7 x3 x1 =
              bindM (step_opcode_mem_ld_reg x7 x3 x1) (fun _ : unit => returnM tt)). {
          clear.
          unfold step_opcode_mem_ld_reg, get_opcode_mem_ld_reg.
          unfold bindM, returnM.
          destruct byte_to_opcode_mem_ld_reg; try reflexivity.
          all: apply Coq.Logic.FunctionalExtensionality.functional_extensionality;
          intros.
          all: destruct check_mem; try reflexivity.
          all: destruct p0.
          all: destruct cmp_ptr32_nullM; try reflexivity.
          all: destruct p0.
          all: destruct b; try reflexivity.
          all: destruct load_mem; try reflexivity.
          all: destruct p0.
          all: destruct upd_reg; try reflexivity.
          all: destruct p0.
          all: reflexivity.
        }
        rewrite Heq; clear Heq.
        correct_forward.

        get_invariant _st.
        get_invariant _addr.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        split.
        reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        intros.
        unfold eval_inv.
        reflexivity.
      + reflexivity.
      + intros. simpl in H0.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold eval_inv, opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_st_imm *)
      eapply correct_statement_switch with (n:= 2).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_immediate _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_addr_ofs _) ... *)
        correct_forward.

        get_invariant _dst64.
        get_invariant _ofs.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_st_imm (rBPFValues.sint32_to_vint x6) x7 x3 x1 =
              bindM (step_opcode_mem_st_imm (rBPFValues.sint32_to_vint x6) x7 x3 x1) (fun _ : unit => returnM tt)). {
          clear.
          unfold step_opcode_mem_st_imm, get_opcode_mem_st_imm.
          unfold bindM, returnM.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality;
          intros.
          destruct byte_to_opcode_mem_st_imm; try reflexivity.
          all: destruct check_mem; try reflexivity.
          all: destruct p0.
          all: destruct cmp_ptr32_nullM; try reflexivity.
          all: destruct p0.
          all: destruct b; try reflexivity.
          all: destruct store_mem_imm; try reflexivity.
          all: destruct p0.
          all: reflexivity.
        }
        rewrite Heq; clear Heq.
        correct_forward.

        get_invariant _st.
        get_invariant _imm.
        get_invariant _addr.
        get_invariant _dst.
        get_invariant _op.
        exists (v::v0::v1::v2::v3::nil).
        unfold eval_inv, correct_get_immediate.match_res, sint32_correct in c0.
        split.
        unfold map_opt, exec_expr. rewrite p0,p1,p2,p3,p4; reflexivity.
        intros; simpl.
        intuition eauto.
        unfold stateless, val32_correct, rBPFValues.sint32_to_vint.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        intros.
        unfold eval_inv.
        reflexivity.
      + reflexivity.
      + intros. simpl in H0.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold eval_inv, opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_st_reg *)
      eapply correct_statement_switch with (n:= 3).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
        correct_forward.

        get_invariant _st.
        get_invariant _src.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
        correct_forward.

        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_addr_ofs _) ... *)
        correct_forward.

        get_invariant _dst64.
        get_invariant _ofs.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_st_reg x6 x8 x3 x1 =
              bindM (step_opcode_mem_st_reg x6 x8 x3 x1) (fun _ : unit => returnM tt)). {
          clear.
          unfold step_opcode_mem_st_reg, get_opcode_mem_st_reg.
          unfold bindM, returnM.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality;
          intros.
          destruct byte_to_opcode_mem_st_reg; try reflexivity.
          all: destruct check_mem; try reflexivity.
          all: destruct p0.
          all: destruct cmp_ptr32_nullM; try reflexivity.
          all: destruct p0.
          all: destruct b; try reflexivity.
          all: destruct store_mem_reg; try reflexivity.
          all: destruct p0.
          all: reflexivity.
        }
        rewrite Heq; clear Heq.
        correct_forward.

        get_invariant _st.
        get_invariant _src64.
        get_invariant _addr.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        intros.
        unfold eval_inv; auto.
      + reflexivity.
      + intros. simpl in H0.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold eval_inv, opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.
    - (**r op_BPF_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          eval_inv (correct_get_opcode.match_res op_BPF_ILLEGAL_INS) n st4 m4 /\
          n = Vint (Int.repr (Z.of_nat i)) /\
          (i <> 0x00 /\ i <> 0x01 /\ i <> 0x02 /\ i <> 0x03 /\ i <> 0x04 /\ i <> 0x05 /\ i <> 0x07)%nat /\
          (i <= 255)%nat /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le4 m4
            (Etempvar _opc Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat i)))).
        { simpl in H0.
          get_invariant _opc.
          unfold correct_get_opcode.match_res in c.
          exists v.
          assert (c':=c).
          unfold opcode_correct in c'.
          destruct c' as (i & V & ILL & RANGE).
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
        repeat match goal with
        | |- context[Coqlib.zeq ?x (Z.of_nat i)] =>
            destruct (Coqlib.zeq x (Z.of_nat i)) ; try lia
        end.
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
        unfold stateless, flag_correct, int_of_flag; simpl.
        intuition congruence.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        unfold eval_inv; auto.
Qed.

End Step.

Close Scope Z_scope.

Existing Instance correct_function_step.