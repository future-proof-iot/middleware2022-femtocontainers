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

From bpf.comm Require Import Regs State.
From compcert Require Import Values.

Definition is_vlong (v: val): Prop :=
  match v with
  | Vlong _ => True
  | _ => False
  end.

Definition register_inv (st: state): Prop :=
  is_vlong (r0_val  (regs_st st)) /\
  is_vlong (r1_val  (regs_st st)) /\
  is_vlong (r2_val  (regs_st st)) /\
  is_vlong (r3_val  (regs_st st)) /\
  is_vlong (r4_val  (regs_st st)) /\
  is_vlong (r5_val  (regs_st st)) /\
  is_vlong (r6_val  (regs_st st)) /\
  is_vlong (r7_val  (regs_st st)) /\
  is_vlong (r8_val  (regs_st st)) /\
  is_vlong (r9_val  (regs_st st)) /\
  is_vlong (r10_val (regs_st st)).

Lemma is_vlong_iff:
  forall v,
    is_vlong v <->
      exists vl,
        v = Vlong vl.
Proof.
  unfold is_vlong; split; intros.
  - destruct v; try intuition.
    exists i; reflexivity.
  - destruct H as (vl & H).
    rewrite H.
    constructor.
Qed.

Lemma reg_inv_init: register_inv init_state.
Proof.
  unfold register_inv, init_state.
  repeat split.
Qed.

Lemma reg_inv_eval_reg:
  forall st r
    (Hreg_inv: register_inv st),
    exists i,
      eval_reg r st = Vlong i.
Proof.
  intros.
  unfold register_inv in Hreg_inv.
  apply is_vlong_iff.
  unfold eval_reg.
  unfold eval_regmap.
  destruct r; intuition.
Qed.

Lemma reg_inv_upd_reg:
  forall st1 st2 r n
    (Hreg_inv: register_inv st1)
    (Halu: upd_reg r (Vlong n) st1 = st2),
      register_inv st2.
Proof.
  unfold register_inv, upd_reg, upd_regmap.
  intros.
  rewrite <- Halu.
  destruct r; simpl; tauto.
Qed.

Lemma reg_inv_upd_flag:
  forall st1 st2 f
    (Hreg_inv: register_inv st1)
    (Hflag: upd_flag f st1 = st2),
      register_inv st2.
Proof.
  unfold register_inv, upd_flag, upd_regmap.
  intros.
  rewrite <- Hflag.
  simpl.
  assumption.
Qed.

Lemma reg_inv_upd_mem:
  forall st1 st2 m
    (Hreg_inv: register_inv st1)
    (Hmem: upd_mem m st1 = st2),
      register_inv st2.
Proof.
  unfold register_inv.
  intros.
  rewrite <- Hmem.
  unfold upd_mem.
  simpl; assumption.
Qed.

Lemma reg_inv_upd_pc:
  forall st1 st2 p
    (Hreg_inv: register_inv st1)
    (Hpc: upd_pc p st1 = st2),
      register_inv st2.
Proof.
  unfold register_inv.
  intros.
  rewrite <- Hpc.
  unfold upd_pc.
  simpl; assumption.
Qed.

Lemma reg_inv_upd_pc_incr:
  forall st1 st2
    (Hreg_inv: register_inv st1)
    (Hpc: upd_pc_incr st1 = st2),
      register_inv st2.
Proof.
  unfold register_inv.
  intros.
  rewrite <- Hpc.
  unfold upd_pc.
  simpl; assumption.
Qed.

Lemma reg_inv_store_reg:
  forall st1 st2 chunk addr src
    (Hreg : register_inv st1)
    (Hstore: store_mem_reg addr chunk (Vlong src) st1 = Some st2),
      register_inv st2.
Proof.
  unfold store_mem_reg, upd_mem, upd_flag, register_inv;
  intros.
  destruct chunk; inversion Hstore; try assumption.
  all: destruct Memory.Mem.storev; inversion H0; intuition.
Qed.

Lemma reg_inv_store_imm:
  forall st1 st2 chunk addr src
    (Hreg : register_inv st1)
    (Hstore: store_mem_imm addr chunk (Vint src) st1 = Some st2),
      register_inv st2.
Proof.
  unfold store_mem_imm, upd_mem, upd_flag, register_inv;
  intros.
  destruct chunk; inversion Hstore; try assumption.
  all: destruct Memory.Mem.storev; inversion H0; intuition.
Qed.