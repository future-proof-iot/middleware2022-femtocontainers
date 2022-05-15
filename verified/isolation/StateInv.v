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

From compcert Require Import Integers Values Memory AST.
From bpf.comm Require Import State Monad rBPFMonadOp.
From bpf.comm Require Import MemRegion rBPFMemType rBPFAST rBPFValues.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv CheckMem.

From Coq Require Import ZArith List Lia.
Import ListNotations.

Open Scope Z_scope.

Definition state_inv (st1 st2: state): Prop :=
  mrs_num st1 = mrs_num st2 /\
  bpf_mrs st1 = bpf_mrs st2 /\
  ins_len st1 = ins_len st2 /\
  ins     st1 = ins     st2.

Lemma step_preserving_state_inv_alu:
  forall st1 st2 a b r s t
    (Hsem : step_alu_binary_operation a b r s st1 = Some (t, st2)),
      state_inv st1 st2.
Proof.
  unfold step_alu_binary_operation.
  unfold eval_src32, eval_reg32, eval_reg, eval_src, upd_reg, State.upd_reg, bindM, returnM.
  intros.
  unfold state_inv, mrs_num, bpf_mrs, ins_len, ins.
  destruct a.
  - destruct s.
    + destruct b.
      all: try
      match goal with
      | H: (if ?X then _ else _ ) _ = _ |- _ =>
        destruct X; [ | inversion H; repeat split; reflexivity]
      end.
      all: try
      match goal with
      | H: match ?X with _ => _ end = _ |- _ =>
        destruct X; inversion H; repeat split; reflexivity
      end.
      destruct Val.divu; [destruct Val.longofintu | ];
          inversion Hsem; repeat split; reflexivity.
      destruct Val.modu; [destruct Val.longofintu | ];
          inversion Hsem; repeat split; reflexivity.
    + destruct b.
      all: try
      match goal with
      | H: (if ?X then _ else _ ) _ = _ |- _ =>
        destruct X; [ | inversion H; repeat split; reflexivity]
      end.
      all: try
      match goal with
      | H: match ?X with _ => _ end = _ |- _ =>
        destruct X; inversion H; repeat split; reflexivity
      end.
      destruct Val.divu; [destruct Val.longofintu | ];
          inversion Hsem; repeat split; reflexivity.
      destruct Val.modu; [destruct Val.longofintu | ];
          inversion Hsem; repeat split; reflexivity.
  - unfold eval_reg in Hsem.
    destruct s.
    + destruct b.
      all: try
      match goal with
      | H: (if ?X then _ else _ ) _ = _ |- _ =>
        destruct X; [ | inversion H; repeat split; reflexivity]
      end.
      all: try
      match goal with
      | H: match ?X with _ => _ end = _ |- _ =>
        destruct X; inversion H; repeat split; reflexivity
      end.
      destruct Val.divlu; [destruct v|]; inversion Hsem; repeat split; reflexivity.
      destruct Val.modlu; [destruct v|]; inversion Hsem; repeat split; reflexivity.
    + destruct b.
      all: try
      match goal with
      | H: (if ?X then _ else _ ) _ = _ |- _ =>
        destruct X; [ | inversion H; repeat split; reflexivity]
      end.
      all: try
      match goal with
      | H: match ?X with _ => _ end = _ |- _ =>
        destruct X; inversion H; repeat split; reflexivity
      end.
      destruct Val.divlu; [destruct v|]; inversion Hsem; repeat split; reflexivity.
      destruct Val.modlu; [destruct v|]; inversion Hsem; repeat split; reflexivity.
Qed.

Lemma step_preserving_state_inv_branch:
  forall st1 st2 c r s o t
    (Hsem : match step_branch_cond c r s st1 with
       | Some (x', st') =>
           (if x'
            then
             fun st : state =>
             if Int.cmpu Clt (Int.add (State.eval_pc st1) o)
                 (Int.repr (Z.of_nat (ins_len st)))
             then Some (tt, State.upd_pc (Int.add (State.eval_pc st1) o) st)
             else None
            else fun st : state => Some (tt, st)) st'
       | None => None
       end = Some (t, st2)),
      state_inv st1 st2.
Proof.
  unfold step_branch_cond.
  unfold eval_src, eval_reg, State.upd_pc, bindM, returnM.
  intros.
  unfold state_inv, mrs_num, bpf_mrs, ins_len, ins.
  destruct s.
  - destruct c.
    all: try destruct s.
    all: match goal with
    | H: (if ?X then _ else _) _ = _ |- _ =>
      destruct X; [| inversion H; repeat split; reflexivity]
    end.
    all: match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X; inversion H; repeat split; reflexivity
    end.
  - destruct c.
    all: try destruct s.
    all: match goal with
    | H: (if ?X then _ else _) _ = _ |- _ =>
      destruct X; [| inversion H; repeat split; reflexivity]
    end.
    all: match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X; inversion H; repeat split; reflexivity
    end.
Qed.

Lemma step_preserving_state_inv_ld:
  forall st1 st2 m r r0 o t
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hsem : step_load_x_operation m r r0 o st1 = Some (t, st2)),
      state_inv st1 st2.
Proof.
  unfold step_load_x_operation.
  unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs, cmp_ptr32_nullM, upd_flag, load_mem, upd_reg, bindM, returnM.
  intros.
  destruct check_mem eqn: Hcheck; [| inversion Hsem].
  apply reg_inv_eval_reg with (r:= r0) in Hreg.
  destruct Hreg as (i & Hreg).
  rewrite Hreg in Hcheck.
  unfold sint32_to_vint in Hcheck; simpl in Hcheck.
  rewrite ! check_memM_P in Hcheck; [| constructor| assumption].
  destruct p.
  inversion Hcheck; subst s.
  clear Hcheck H0.
  destruct cmp_ptr32_null; [| inversion Hsem].

  unfold state_inv, mrs_num, bpf_mrs, ins_len, ins.

  destruct b.
  inversion Hsem.
  repeat split; reflexivity.
  destruct State.load_mem; inversion Hsem.
  destruct v0; inversion Hsem.
  repeat split; reflexivity.
Qed.

Lemma step_preserving_inv_st:
  forall st1 st2 m r s o t
    (Hreg_inv : register_inv st1)
    (Hmem_inv : memory_inv st1)
    (Hsem : step_store_operation m r s o st1 = Some (t, st2)),
      state_inv st1 st2.
Proof.
  unfold step_store_operation.
  unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs, cmp_ptr32_nullM, upd_flag, load_mem, upd_reg, bindM, returnM.
  intros.
  unfold state_inv, mrs_num, bpf_mrs, ins_len, ins.
  destruct s.
  - apply reg_inv_eval_reg with (r:= r) in Hreg_inv.
    destruct Hreg_inv as (i & Hreg).
    rewrite Hreg in Hsem.
    unfold sint32_to_vint in Hsem; simpl in Hsem.
    destruct check_mem eqn: Hcheck; [| inversion Hsem].
    rewrite ! check_memM_P in Hcheck; [| constructor| assumption].
    destruct p.
    inversion Hcheck; subst s.
    clear Hcheck H0.
    destruct cmp_ptr32_null; [| inversion Hsem].
    destruct b.
    + inversion Hsem.
      repeat split; reflexivity.
    + unfold store_mem_reg, State.store_mem_reg in Hsem.
      destruct m; inversion Hsem.
      all: destruct Mem.storev; inversion H0.
      all: repeat split; reflexivity.
  - apply reg_inv_eval_reg with (r:= r) in Hreg_inv.
    destruct Hreg_inv as (ri & Hreg).
    rewrite Hreg in Hsem.
    unfold sint32_to_vint in Hsem; simpl in Hsem.
    destruct check_mem eqn: Hcheck; [| inversion Hsem].
    rewrite ! check_memM_P in Hcheck; [| constructor| assumption].
    destruct p.
    inversion Hcheck; subst s.
    clear Hcheck H0.
    destruct cmp_ptr32_null; [| inversion Hsem].
    destruct b.
    + inversion Hsem.
      repeat split; reflexivity.
    + unfold store_mem_imm, State.store_mem_imm in Hsem.
      destruct m; inversion Hsem.
      all: destruct Mem.storev; inversion H0.
      all: repeat split; reflexivity.
Qed.



From bpf.verifier.comm Require Import state.
Definition state_include (st: state.state) (ST: State.state): Prop :=
  state.ins_len st = State.ins_len ST /\ state.ins st = State.ins ST.

Lemma state_include_upd_pc:
  forall (st: state.state) (st1 st2: State.state) p,
    state_include st st1 ->
    State.upd_pc p st1 = st2 ->
      state_include st st2.
Proof.
  unfold state_include.
  unfold State.upd_pc.
  intros.
  destruct H.
  rewrite H, H1.
  rewrite <- H0.
  unfold State.ins_len, State.ins.
  split; reflexivity.
Qed.

Lemma state_include_upd_pc_incr:
  forall (st: state.state) (st1 st2: State.state),
    state_include st st1 ->
    State.upd_pc_incr st1 = st2 ->
      state_include st st2.
Proof.
  unfold state_include.
  unfold State.upd_pc_incr.
  intros.
  destruct H.
  rewrite H, H1.
  rewrite <- H0.
  unfold State.ins_len, State.ins.
  split; reflexivity.
Qed.

Lemma state_include_upd_reg:
  forall (st: state.state) (st1 st2: State.state) (r : Regs.reg) (n : int64),
    state_include st st1 ->
    State.upd_reg r (Vlong n) st1 = st2 ->
      state_include st st2.
Proof.
  unfold state_include.
  unfold State.upd_reg.
  intros.
  destruct H.
  rewrite H, H1.
  rewrite <- H0.
  unfold State.ins_len, State.ins.
  split; reflexivity.
Qed.

Lemma state_include_upd_flag:
  forall (st: state.state) (st1 st2: State.state) (f : Flag.bpf_flag),
    state_include st st1 ->
    State.upd_flag f st1 = st2 ->
      state_include st st2.
Proof.
  unfold state_include.
  unfold State.upd_flag.
  intros.
  destruct H.
  rewrite H, H1.
  rewrite <- H0.
  unfold State.ins_len, State.ins.
  split; reflexivity.
Qed.

Lemma state_include_store_reg:
  forall (st: state.state) (st1 st2 : State.state) (chunk : memory_chunk) (addr : val) (src : int64),
    is_well_chunk chunk ->
    state_include st st1 ->
    State.store_mem_reg addr chunk (Vlong src) st1 = Some st2 ->
      state_include st st2.
Proof.
  unfold store_mem_reg, upd_mem, upd_flag, state_include;
  intros.
  destruct chunk; inversion H1; try assumption.
  all: destruct Mem.storev; inversion H3; intuition.
Qed.

Lemma state_include_store_imm:
  forall (st: state.state) (st1 st2 : State.state) chunk addr src,
    state_include st st1 ->
    State.store_mem_imm addr chunk (Vint src) st1 = Some st2 ->
      state_include st st2.
Proof.
  unfold store_mem_imm, upd_mem, upd_flag, state_include;
  intros.
  destruct chunk; inversion H0; try assumption.
  all: destruct Mem.storev; inversion H2; intuition.
Qed.
