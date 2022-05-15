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

From compcert Require Import Integers Values AST Memory Memtype.
From bpf.comm Require Import BinrBPF State Monad rBPFMonadOp.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv VerifierInv CheckMem StateInv IsolationLemma.

From Coq Require Import ZArith Lia.

Open Scope Z_scope.

Axiom call_inv: forall st st1 st2 b ofs res
  (Hreg : register_inv st1)
  (Hmem : memory_inv st1)
  (Hst0 : state_include st st1)
  (Hcall: exec_function (Vptr b ofs) st1 = Some (res, st2)),
    register_inv st2 /\ memory_inv st2 /\ state_include st st2.

Lemma step_preserving_inv:
  forall st st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem: step st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.
  unfold step.
  unfold_monad.
  intros.
  match goal with
  | H: match (if ?X then _ else _) with | _ => _ end = Some _ |- _ =>
    destruct X; [| inversion H]
  end.
  destruct (Decode.decode _) in Hsem; [| inversion Hsem].
  destruct i in Hsem.
  - (* BPF_NEG *)
    apply reg_inv_eval_reg with (r:= r) in Hreg as Heval_reg.
    destruct Heval_reg as (vl & Heval_reg).
    destruct a; rewrite Heval_reg in Hsem; simpl in Hsem.
    + inversion Hsem.
      split.
      eapply reg_inv_upd_reg; eauto.
      split.
      eapply mem_inv_upd_reg; eauto.
      eapply state_include_upd_reg; eauto.
    + inversion Hsem.
      split.
      eapply reg_inv_upd_reg; eauto.
      split.
      eapply mem_inv_upd_reg; eauto.
      eapply state_include_upd_reg; eauto.
  - (* BPF_BINARY *)
    eapply step_preserving_inv_alu; eauto.
  - (* BPF_JA *)
    match goal with
    | H : (if ?X then _ else _) = _ |- _ =>
      destruct X; inversion H
    end.
    split; [eapply reg_inv_upd_pc; eauto |
      split; [eapply mem_inv_upd_pc; eauto | eapply state_include_upd_pc; eauto]].
  - (* BPF_JUMP *)
    eapply step_preserving_inv_branch; eauto.
  - (* BPF_LDDW_low *)
    unfold rBPFValues.sint32_to_vint in Hsem.
    simpl in Hsem.
    inversion Hsem; clear Hsem.
    split; [eapply reg_inv_upd_reg; eauto |
        split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]].
  - (* BPF_LDDW_high *)
    unfold rBPFValues.sint32_to_vint in Hsem.
    destruct Val.orl; inversion Hsem.
    split; [eapply reg_inv_upd_reg; eauto |
        split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]].
  - (* BPF_LDX *)
    eapply step_preserving_inv_ld; eauto.
  - (* BPF_ST *)
    eapply step_preserving_inv_st; eauto.
  - (* BPF_CALL *)
    assert (Hget_call: forall i, exists ptr,
      _bpf_get_call (Vint i) st1 = Some (ptr, st1) /\
      (ptr = Vnullptr \/ (exists b ofs, ptr = Vptr b ofs /\ ((Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs)
        || Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs - 1)) = true)%bool))). {
      intro.
      apply lemma_bpf_get_call.
    }
    specialize (Hget_call (Int.repr (Int64.unsigned (Int64.repr (Int.signed i))))).
    destruct Hget_call as (ptr & Hget_call & Hres).
    rewrite Hget_call in Hsem.
    destruct Hres as [Hnull | (b & ofs & Hptr & Hvalid)]; unfold cmp_ptr32_nullM, rBPFValues.cmp_ptr32_null in Hsem; subst.
    + simpl in Hsem.
      rewrite Int.eq_true in Hsem.
      inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
    + destruct Val.cmpu_bool eqn:cmp; [| inversion Hsem].
      destruct b0.
      * inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
      * assert (Hexec: forall b ofs st1,
      exists v st2, exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\ rBPFValues.cmp_ptr32_null (State.eval_mem st1) (Vptr b ofs) = Some false) by apply lemma_exec_function0.
        specialize (Hexec b ofs st1).
        destruct Hexec as (res & st' & Hexec & _).
        rewrite Hexec in Hsem.
        eapply call_inv in Hexec; eauto.
        destruct res; inversion Hsem.
        destruct Hexec as (Hreg_st & Hmem_st & Hver_st).
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]].
  - (* BPF_RET *)
    inversion Hsem.
    split; [eapply reg_inv_upd_flag; eauto |
      split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
  - (* BPF_ERR *)
    inversion Hsem.
    split; [eapply reg_inv_upd_flag; eauto |
      split; [ eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
Qed.

Lemma bpf_interpreter_aux_preserving_inv:
  forall st fuel st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem: bpf_interpreter_aux fuel st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.
  induction fuel; intros.
  - simpl in Hsem.
    inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
  - simpl in Hsem.
    unfold eval_ins_len, eval_pc, eval_flag, upd_pc_incr, bindM, returnM in Hsem.
    destruct Int.ltu.
    + destruct step eqn: Hstep; [| inversion Hsem].
      destruct p.
      destruct Flag.flag_eq.
      * destruct Int.ltu.
        {
          eapply step_preserving_inv in Hstep; eauto.
          destruct Hstep as (Hreg_s & Hmem_s & Hver_s).
          assert (Hinv: register_inv (State.upd_pc_incr s) /\ memory_inv (State.upd_pc_incr s) /\ state_include st (State.upd_pc_incr s)). {
            split; [eapply reg_inv_upd_pc_incr; eauto |
          split; [eapply mem_inv_upd_pc_incr; eauto | eapply state_include_upd_pc_incr; eauto]].
          }
          destruct Int.cmpu; [| inversion Hsem].
          destruct Hinv as (Hreg_s' & Hmem_s' & Hver_s').
          specialize (IHfuel (State.upd_pc_incr s) st2 t Hreg_s' Hmem_s' Hver_s' Hsem).
          congruence.
        }
        {
          eapply step_preserving_inv in Hstep; eauto.
          destruct Hstep as (Hreg_s & Hmem_s & Hver_s).
          assert (Hinv: register_inv (State.upd_pc_incr s) /\ memory_inv (State.upd_pc_incr s) /\ state_include st (State.upd_pc_incr s)). {
            split; [eapply reg_inv_upd_pc_incr; eauto |
          split; [eapply mem_inv_upd_pc_incr; eauto | eapply state_include_upd_pc_incr; eauto]].
          }
          inversion Hsem.
          clear - Hreg_s Hmem_s Hver_s.

          split; [eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
        }

      * inversion Hsem. subst.
        eapply step_preserving_inv in Hstep; eauto.
    + inversion Hsem; split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
Qed.

Theorem bpf_interpreter_preserving_inv:
  forall st fuel st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem: bpf_interpreter fuel st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.
  intros.
  unfold bpf_interpreter in Hsem.
  unfold eval_mem_regions, get_mem_region, get_start_addr, upd_reg, eval_flag, eval_reg, bindM, returnM in Hsem.
  destruct (0 <? mrs_num st1)%nat; [| inversion Hsem].
  destruct List.nth_error; [| inversion Hsem].
  destruct Val.longofintu; inversion Hsem.
  destruct bpf_interpreter_aux eqn: Haux; [| inversion Hsem].
  destruct p.
  eapply bpf_interpreter_aux_preserving_inv in Haux; eauto.
  - destruct Flag.flag_eq.
    + inversion H0.
      subst.
      auto.
    + inversion H0.
      subst.
      auto.
  - destruct Flag.flag_eq.
    + eapply reg_inv_upd_reg; eauto.
    + eapply reg_inv_upd_reg; eauto.
Qed.