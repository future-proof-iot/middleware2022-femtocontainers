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

From Coq Require Import Logic.FunctionalExtensionality ZArith Lia.
From compcert Require Import Integers Values Memory Memdata.

From bpf.comm Require Import State Monad rBPFMonadOp.
From bpf.dxmodel Require Import DxInstructions.

From bpf.monadicmodel Require Import Opcode rBPFInterpreter.

Ltac unfold_monad :=
  match goal with
  | |- _ =>
    unfold bindM, returnM
  end.

Ltac unfold_dx_type :=
  match goal with
  | |- _ =>
    unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag, DxMonad.eval_ins;
    unfold BinrBPF.get_opcode;
    unfold DxIntegers.sint32_t, DxIntegers.int64_t, DxNat.nat8, DxValues.val64_t, DxValues.valu32_t, DxValues.vals32_t;
  unfold_monad
  end.

Ltac unfold_dx_name :=
  match goal with
  | |- _ =>
    unfold DxNat.nat8_zero, DxNat.nat8_0x08, DxNat.nat8_0x07, DxIntegers.int64_0xff, DxIntegers.int64_32, DxNat.nat8_0xf0, DxIntegers.int64_64, DxValues.val32_64, DxIntegers.int64_48, DxNat.nat8_0xff, DxValues.val64_zero, Regs.val64_zero, DxIntegers.int32_0, DxIntegers.int32_64
  end.

Ltac unfold_dx :=
  match goal with
  | |- _ =>
    unfold get_opcode_ins, get_opcode, Opcode.byte_to_opcode;
    unfold_dx_name; unfold_dx_type
  end.

Ltac destruct_if_reflexivity :=
  match goal with
  | |- context[(if ?X then _ else _) ] =>
    destruct X; [| reflexivity]
  end.

Open Scope Z_scope.

Lemma equivalence_between_coq_and_dx_step:
  DxInstructions.step = rBPFInterpreter.step.
Proof.
  unfold rBPFInterpreter.step, DxInstructions.step.
  apply functional_extensionality.
  unfold_dx.
  intros.
  unfold DxInstructions.get_opcode_ins, DxInstructions.get_opcode, eval_pc, eval_ins.
  unfold_dx.
  unfold DxInstructions.get_dst, DxInstructions.get_src64, DxInstructions.get_src32, DxInstructions.get_immediate, DxInstructions.eval_immediate, DxInstructions.step_opcode_alu64, DxInstructions.get_src; unfold_dx.
  unfold get_dst, DxInstructions.step_opcode_mem_ld_imm; unfold_dx.
  unfold DxInstructions.get_opcode_mem_ld_imm, DxInstructions.get_immediate; unfold_dx.
  unfold DxMonad.int64_to_dst_reg, DxNat.nat2int, DxIntegers.int32_8, DxValues.Val_ulongofslong, DxValues.Val_slongofint, DxMonad.int64_to_src_reg, DxInstructions.get_opcode_alu64, DxInstructions.reg64_to_reg32, DxNat.nat8_0x87, DxInstructions.step_opcode_alu32, DxInstructions.get_offset, DxInstructions.step_opcode_branch, DxIntegers.int32_1, DxIntegers.int32_32, DxInstructions.step_opcode_mem_ld_reg, DxInstructions.step_opcode_mem_ld_imm, DxInstructions.step_opcode_mem_st_reg, DxInstructions.step_opcode_mem_st_imm, DxInstructions.get_addr_ofs.
  destruct_if_reflexivity.
  destruct int64_to_dst_reg; [| reflexivity].
  destruct p.
  destruct (match
    Nat.land
      (Z.to_nat (Int64.unsigned (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255))))
      7
  with
  | 0%nat => op_BPF_Mem_ld_imm
  | 1%nat => op_BPF_Mem_ld_reg
  | 2%nat => op_BPF_Mem_st_imm
  | 3%nat => op_BPF_Mem_st_reg
  | 4%nat => op_BPF_ALU32
  | 5%nat => op_BPF_Branch
  | 7%nat => op_BPF_ALU64
  | _ => op_BPF_ILLEGAL_INS
  end) eqn: Hopcode; unfold eval_reg, get_src64, get_src32; unfold_dx.
  - destruct_if_reflexivity.
    unfold step_opcode_alu64.
    unfold get_opcode_alu64.
    unfold get_immediate, eval_immediate, reg64_to_reg32.
    unfold_dx.
    unfold rBPFValues.sint32_to_vint.
    destruct byte_to_opcode_alu64; try destruct_if_reflexivity; try(destruct upd_reg; reflexivity).
    reflexivity.
  - destruct_if_reflexivity.
    unfold DxInstructions.get_opcode_alu32, DxValues.val32_zero, DxValues.val32_32, DxNat.nat8_0x84.
    unfold reg64_to_reg32, get_immediate.
    unfold step_opcode_alu32.
    unfold get_opcode_alu32, Vzero, DxIntegers.int32_32.
    unfold_dx.
    unfold rBPFValues.sint32_to_vint.
    destruct byte_to_opcode_alu32; try destruct_if_reflexivity; try(destruct upd_reg; reflexivity).
    reflexivity.
  - destruct_if_reflexivity.
    unfold DxInstructions.get_opcode_branch, DxNat.nat8_0x05, DxMonad.upd_pc, DxNat.nat8_0x85, DxMonad._bpf_get_call, DxMonad.cmp_ptr32_nullM, DxMonad.exec_function, DxNat.nat8_0x95.
    unfold get_offset, get_immediate, eval_immediate, step_opcode_branch, get_opcode_branch.
    unfold_dx.
    destruct byte_to_opcode_branch; try destruct_if_reflexivity; try(destruct upd_pc; reflexivity).
    all: try reflexivity.
  - unfold get_immediate, step_opcode_mem_ld_imm, get_opcode_mem_ld_imm; unfold_dx.
    destruct byte_to_opcode_mem_ld_imm; try destruct_if_reflexivity; try reflexivity.
  - unfold DxInstructions.get_opcode_mem_ld_reg, DxInstructions.check_mem, DxMonad.cmp_ptr32_nullM, DxMonad.load_mem, get_src, get_offset, get_addr_ofs, step_opcode_mem_ld_reg, DxInstructions.is_well_chunk_bool, DxMonad.eval_mrs_num, DxMonad.eval_mrs_regions, DxInstructions.check_mem_aux, DxValues.valptr_null, get_opcode_mem_ld_reg; unfold_dx.
    destruct int64_to_src_reg; [| reflexivity].
    destruct p.
    destruct byte_to_opcode_mem_ld_reg; try reflexivity.
  - unfold DxInstructions.get_opcode_mem_st_imm, DxInstructions.check_mem, DxMonad.cmp_ptr32_nullM, DxMonad.store_mem_imm, get_offset, get_immediate, get_addr_ofs, step_opcode_mem_st_imm, DxInstructions.is_well_chunk_bool, DxMonad.eval_mrs_num, DxMonad.eval_mrs_regions, DxInstructions.check_mem_aux, DxValues.valptr_null, get_opcode_mem_st_imm; unfold_dx.
    destruct byte_to_opcode_mem_st_imm; try reflexivity.
  - unfold DxInstructions.get_opcode_mem_st_reg, DxInstructions.check_mem, DxMonad.cmp_ptr32_nullM, DxMonad.store_mem_reg, get_src, get_offset, get_addr_ofs, step_opcode_mem_st_reg, DxInstructions.is_well_chunk_bool, DxMonad.eval_mrs_num, DxMonad.eval_mrs_regions, DxInstructions.check_mem_aux, DxValues.valptr_null, get_opcode_mem_st_reg; unfold_dx.
    destruct int64_to_src_reg; [| reflexivity].
    destruct p.
    destruct byte_to_opcode_mem_st_reg; try reflexivity.
  - reflexivity.
Qed.

Lemma equivalence_between_coq_and_dx_aux:
  forall f,
    rBPFInterpreter.bpf_interpreter_aux f = DxInstructions.bpf_interpreter_aux f.
Proof.
  unfold rBPFInterpreter.bpf_interpreter_aux, DxInstructions.bpf_interpreter_aux.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag.
  unfold DxIntegers.sint32_t.
  unfold DxIntegers.int32_0.
  rewrite equivalence_between_coq_and_dx_step.
  reflexivity.
Qed.

Theorem equivalence_between_coq_and_dx_dx:
  forall f,
    rBPFInterpreter.bpf_interpreter f = DxInstructions.bpf_interpreter f.
Proof.
  intros.
  unfold rBPFInterpreter.bpf_interpreter, DxInstructions.bpf_interpreter.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM.
  rewrite equivalence_between_coq_and_dx_aux.
  reflexivity.
Qed.

Close Scope Z_scope.