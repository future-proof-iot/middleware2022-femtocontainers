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

From bpf.comm Require Import rBPFAST List64 MemRegion Regs Flag State.

From bpf.monadicmodel Require Import Opcode.

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CommonLib.
From bpf.simulation Require Import MatchState.

Definition val_ptr_correct {S:special_blocks} (x:val) (v: val) (st: State.state) (m:Memory.Mem.mem) :=
  x = v /\
  match_state st m.

Open Scope nat_scope.
Definition is_state_handle {S: special_blocks} (v: val) := v = Vptr st_blk Ptrofs.zero.

Definition is_illegal_alu64_ins (i:nat): Prop :=
  ((Nat.land i 240) <> 0x00) /\
  ((Nat.land i 240) <> 0x10) /\
  ((Nat.land i 240) <> 0x20) /\
  ((Nat.land i 240) <> 0x30) /\
  ((Nat.land i 240) <> 0x40) /\
  ((Nat.land i 240) <> 0x50) /\
  ((Nat.land i 240) <> 0x60) /\
  ((Nat.land i 240) <> 0x70) /\
  ((Nat.land i 240) <> 0x80) /\
  ((Nat.land i 240) <> 0x90) /\
  ((Nat.land i 240) <> 0xa0) /\
  ((Nat.land i 240) <> 0xb0) /\
  ((Nat.land i 240) <> 0xc0).

Definition opcode_alu64_correct (opcode: opcode_alu64) (v: val) :=
  match opcode with
  | op_BPF_ADD64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x07 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x0f 240)))
  | op_BPF_SUB64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x17 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x1f 240)))
  | op_BPF_MUL64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x27 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x2f 240)))
  | op_BPF_DIV64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x37 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x3f 240)))
  | op_BPF_OR64  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x47 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x4f 240)))
  | op_BPF_AND64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x57 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x5f 240)))
  | op_BPF_LSH64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x67 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x6f 240)))
  | op_BPF_RSH64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x77 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x7f 240)))
  | op_BPF_NEG64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x87 240)))
  | op_BPF_MOD64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x97 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x9f 240)))
  | op_BPF_XOR64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xa7 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xaf 240)))
  | op_BPF_MOV64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xb7 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xbf 240)))
  | op_BPF_ARSH64=> v = Vint (Int.repr (Z.of_nat (Nat.land 0xc7 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xcf 240)))
  | op_BPF_ALU64_ILLEGAL_INS => exists i, v = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\ is_illegal_alu64_ins i
  end.

Definition is_illegal_alu32_ins (i:nat): Prop :=
  ((Nat.land i 240) <> 0x00) /\
  ((Nat.land i 240) <> 0x10) /\
  ((Nat.land i 240) <> 0x20) /\
  ((Nat.land i 240) <> 0x30) /\
  ((Nat.land i 240) <> 0x40) /\
  ((Nat.land i 240) <> 0x50) /\
  ((Nat.land i 240) <> 0x60) /\
  ((Nat.land i 240) <> 0x70) /\
  ((Nat.land i 240) <> 0x80) /\
  ((Nat.land i 240) <> 0x90) /\
  ((Nat.land i 240) <> 0xa0) /\
  ((Nat.land i 240) <> 0xb0) /\
  ((Nat.land i 240) <> 0xc0).

Definition opcode_alu32_correct (opcode: opcode_alu32) (v: val) :=
  match opcode with
  | op_BPF_ADD32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x04 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x0c 240)))
  | op_BPF_SUB32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x14 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x1c 240)))
  | op_BPF_MUL32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x24 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x2c 240)))
  | op_BPF_DIV32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x34 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x3c 240)))
  | op_BPF_OR32  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x44 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x4c 240)))
  | op_BPF_AND32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x54 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x5c 240)))
  | op_BPF_LSH32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x64 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x6c 240)))
  | op_BPF_RSH32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x74 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x7c 240)))
  | op_BPF_NEG32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x84 240)))
  | op_BPF_MOD32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x94 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x9c 240)))
  | op_BPF_XOR32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xa4 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xac 240)))
  | op_BPF_MOV32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xb4 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xbc 240)))
  | op_BPF_ARSH32=> v = Vint (Int.repr (Z.of_nat (Nat.land 0xc4 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xcc 240)))
  | op_BPF_ALU32_ILLEGAL_INS => exists i, v = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\ is_illegal_alu32_ins i
  end.

Definition is_illegal_jmp_ins (i:nat): Prop :=
  ((Nat.land i 240) <> 0x00) /\
  ((Nat.land i 240) <> 0x10) /\
  ((Nat.land i 240) <> 0x20) /\
  ((Nat.land i 240) <> 0x30) /\
  ((Nat.land i 240) <> 0x40) /\
  ((Nat.land i 240) <> 0x50) /\
  ((Nat.land i 240) <> 0x60) /\
  ((Nat.land i 240) <> 0x70) /\
  ((Nat.land i 240) <> 0x80) /\
  ((Nat.land i 240) <> 0x90) /\
  ((Nat.land i 240) <> 0xa0) /\
  ((Nat.land i 240) <> 0xb0) /\
  ((Nat.land i 240) <> 0xc0) /\
  ((Nat.land i 240) <> 0xd0).

Definition opcode_branch_correct (opcode: opcode_branch) (v: val) :=
  match opcode with
  | op_BPF_JA    => v = Vint (Int.repr (Z.of_nat (Nat.land 0x05 240)))
  | op_BPF_JEQ   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x15 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x1d 240)))
  | op_BPF_JGT   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x25 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x2d 240)))
  | op_BPF_JGE   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x35 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x3d 240)))
  | op_BPF_JLT   => v = Vint (Int.repr (Z.of_nat (Nat.land 0xa5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xad 240)))
  | op_BPF_JLE   => v = Vint (Int.repr (Z.of_nat (Nat.land 0xb5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xbd 240)))
  | op_BPF_JSET  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x45 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x4d 240)))
  | op_BPF_JNE   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x55 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x5d 240)))
  | op_BPF_JSGT  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x65 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x6d 240)))
  | op_BPF_JSGE  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x75 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x7d 240)))
  | op_BPF_JSLT  => v = Vint (Int.repr (Z.of_nat (Nat.land 0xc5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xcd 240)))
  | op_BPF_JSLE  => v = Vint (Int.repr (Z.of_nat (Nat.land 0xd5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xdd 240)))
  | op_BPF_CALL  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x85 240)))
  | op_BPF_RET   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x95 240)))
  | op_BPF_JMP_ILLEGAL_INS => exists i, v = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\ is_illegal_jmp_ins i
  end.

Definition opcode_mem_ld_imm_correct (opcode: opcode_mem_ld_imm) (v: val) :=
  match opcode with
  | op_BPF_LDDW_low  => v = Vint (Int.repr (Z.of_nat 0x18))
  | op_BPF_LDDW_high => v = Vint (Int.repr (Z.of_nat 0x10))
  | op_BPF_LDX_IMM_ILLEGAL_INS =>
    exists i,
      v = Vint (Int.repr (Z.of_nat i)) /\
      (i <> 0x18 /\ i <> 0x10) /\
      i <= 255
  end.

Definition opcode_mem_ld_reg_correct (opcode: opcode_mem_ld_reg) (v: val) :=
  match opcode with
  | op_BPF_LDXW  => v = Vint (Int.repr (Z.of_nat 0x61))
  | op_BPF_LDXH  => v = Vint (Int.repr (Z.of_nat 0x69))
  | op_BPF_LDXB  => v = Vint (Int.repr (Z.of_nat 0x71))
  | op_BPF_LDXDW => v = Vint (Int.repr (Z.of_nat 0x79))
  | op_BPF_LDX_REG_ILLEGAL_INS =>
    exists i,
      v = Vint (Int.repr (Z.of_nat i)) /\
      (i <> 0x61 /\ i <> 0x69 /\ i <> 0x71 /\ i <> 0x79) /\
      i <= 255
  end.

Definition opcode_mem_st_imm_correct (opcode: opcode_mem_st_imm) (v: val) :=
  match opcode with
  | op_BPF_STW  => v = Vint (Int.repr (Z.of_nat 0x62))
  | op_BPF_STH  => v = Vint (Int.repr (Z.of_nat 0x6a))
  | op_BPF_STB  => v = Vint (Int.repr (Z.of_nat 0x72))
  | op_BPF_STDW => v = Vint (Int.repr (Z.of_nat 0x7a))
  | op_BPF_ST_ILLEGAL_INS =>
    exists i,
      v = Vint (Int.repr (Z.of_nat i)) /\
      (i <> 0x62 /\ i <> 0x6a /\ i <> 0x72 /\ i <> 0x7a) /\
      i <= 255
  end.

Definition opcode_mem_st_reg_correct (opcode: opcode_mem_st_reg) (v: val) :=
  match opcode with
  | op_BPF_STXW  => v = Vint (Int.repr (Z.of_nat 0x63))
  | op_BPF_STXH  => v = Vint (Int.repr (Z.of_nat 0x6b))
  | op_BPF_STXB  => v = Vint (Int.repr (Z.of_nat 0x73))
  | op_BPF_STXDW => v = Vint (Int.repr (Z.of_nat 0x7b))
  | op_BPF_STX_ILLEGAL_INS =>
    exists i,
      v = Vint (Int.repr (Z.of_nat i)) /\
      (i <> 0x63 /\ i <> 0x6b /\ i <> 0x73 /\ i <> 0x7b) /\
      i <= 255
  end.

Definition opcode_step_correct (op: opcode) (v: val) :=
  match op with
  | op_BPF_ALU64   (**r 0xX7 / 0xXf *) => v = Vint (Int.repr (Z.of_nat 0x07))
  | op_BPF_ALU32   (**r 0xX4 / 0xXc *) => v = Vint (Int.repr (Z.of_nat 0x04))
  | op_BPF_Branch  (**r 0xX5 / 0xXd *) => v = Vint (Int.repr (Z.of_nat 0x05))
  | op_BPF_Mem_ld_imm  (**r 0xX8 *)    => v = Vint (Int.repr (Z.of_nat 0x00))
  | op_BPF_Mem_ld_reg  (**r 0xX1/0xX9 *) => v = Vint (Int.repr (Z.of_nat 0x01))
  | op_BPF_Mem_st_imm  (**r 0xX2/0xXa *) => v = Vint (Int.repr (Z.of_nat 0x02))
  | op_BPF_Mem_st_reg  (**r 0xX3/0xXb *) => v = Vint (Int.repr (Z.of_nat 0x03))

  | op_BPF_ILLEGAL_INS =>
    exists i,
      v = Vint (Int.repr (Z.of_nat i)) /\
      (i <> 0x00 /\ i <> 0x01 /\ i <> 0x02 /\ i <> 0x03 /\ i <> 0x04 /\ i <> 0x05 /\ i <> 0x07) /\
      i <= 255
  end.

Close Scope nat_scope.


Definition mr_correct {S:special_blocks} (mr: memory_region) (v: val) (st: State.state) (m:Memory.Mem.mem) :=
  List.In mr (bpf_mrs st) /\
  match_region st_blk mrs_blk ins_blk mr v st m /\
  match_state  st m.

Definition mrs_correct (S: special_blocks) (mrs: list memory_region) (v: val) (st: State.state) (m:Memory.Mem.mem) :=
  v = Vptr mrs_blk Ptrofs.zero /\
  mrs = (bpf_mrs st) /\
  match_regions st_blk mrs_blk ins_blk st m /\
  match_state  st m.
