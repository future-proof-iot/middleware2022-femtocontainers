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

From compcert Require Import Integers Values AST Ctypes.
From Coq Require Import ZArith.
From dx.Type Require Bool Nat.

From bpf.comm Require Import rBPFValues BinrBPF.
From bpf.dxcomm Require Import DxIntegers DxNat.
From bpf.verifier.comm Require Import state.
From bpf.verifier.synthesismodel Require Import opcode_synthesis.
From bpf.verifier.dxmodel Require Import Dxmonad.

Open Scope nat_scope.
Open Scope monad_scope.

Definition is_dst_R0 (i: int64_t) : M bool := returnM (is_dst_R0' i).

Definition is_well_dst (i: int64_t) : M bool := returnM (is_well_dst' i).

Definition is_well_src (i: int64_t) : M bool := returnM (is_well_src' i).

Definition is_well_jump (pc len: nat) (ofs: sint32_t) : M bool := returnM (is_well_jump' pc len ofs).

Definition is_not_div_by_zero (i: int64_t) : M bool := returnM (is_not_div_by_zero' i).

Definition is_not_div_by_zero64 (i: int64_t) : M bool := returnM (is_not_div_by_zero64' i).

Definition is_shift_range (i: int64_t) (upper: uint32_t): M bool := returnM (is_shift_range' i upper).

Definition is_shift_range64 (i: int64_t) (upper: uint32_t): M bool := returnM (is_shift_range64' i upper).

Definition get_opcode (ins: int64_t): M nat8 := returnM (get_opcode ins).

Definition get_offset (i: int64_t): M sint32_t := returnM (get_offset i).

Definition bpf_verifier_opcode_alu32_imm (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_alu32_imm op with
  | DIV32_IMM
  | MOD32_IMM => (**r DIV_IMM *)
    do b <-- is_not_div_by_zero ins;
      returnM b
  | LSH32_IMM
  | RSH32_IMM
  | ARSH32_IMM => (**r SHIFT_IMM *)
    do b <-- is_shift_range ins int32_32;
      returnM b
  | ADD32_IMM
  | SUB32_IMM
  | MUL32_IMM
  | OR32_IMM
  | AND32_IMM
  | NEG32_IMM
  | XOR32_IMM
  | MOV32_IMM => (**r ALU_IMM *)
    returnM true
  | ALU32_IMM_ILLEGAL => returnM false
  end.

Definition bpf_verifier_opcode_alu32_reg (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_alu32_reg op with
  | DIV32_REG
  | MOD32_REG
  | LSH32_REG
  | RSH32_REG
  | ARSH32_REG
  | ADD32_REG
  | SUB32_REG
  | MUL32_REG
  | OR32_REG
  | AND32_REG
  | XOR32_REG
  | MOV32_REG => (**r ALU_REG *)
    do b <-- is_well_src ins;
      returnM b
  | ALU32_REG_ILLEGAL => returnM false
  end.

Definition bpf_verifier_opcode_alu64_imm (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_alu64_imm op with
  | DIV64_IMM
  | MOD64_IMM => (**r DIV_IMM *)
    do b <-- is_not_div_by_zero64 ins;
      returnM b
  | LSH64_IMM
  | RSH64_IMM
  | ARSH64_IMM => (**r SHIFT_IMM *)
    do b <-- is_shift_range64 ins int32_64;
      returnM b
  | ADD64_IMM
  | SUB64_IMM
  | MUL64_IMM
  | OR64_IMM
  | AND64_IMM
  | NEG64_IMM
  | XOR64_IMM
  | MOV64_IMM => (**r ALU_IMM *)
    returnM true
  | ALU64_IMM_ILLEGAL => returnM false
  end.

Definition bpf_verifier_opcode_alu64_reg (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_alu64_reg op with
  | DIV64_REG
  | MOD64_REG
  | LSH64_REG
  | RSH64_REG
  | ARSH64_REG
  | ADD64_REG
  | SUB64_REG
  | MUL64_REG
  | OR64_REG
  | AND64_REG
  | XOR64_REG
  | MOV64_REG => (**r ALU_REG *)
    do b <-- is_well_src ins;
      returnM b
  | ALU64_REG_ILLEGAL => returnM false
  end.

Definition bpf_verifier_opcode_branch_imm (pc len: nat) (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_branch_imm op with
  | JA_IMM
  | JEQ_IMM
  | JGT_IMM
  | JGE_IMM
  | JLT_IMM
  | JLE_IMM
  | JSET_IMM
  | JNE_IMM
  | JSGT_IMM
  | JSGE_IMM
  | JSLT_IMM
  | JSLE_IMM =>
    do ofs <-- get_offset ins;
    do b <-- is_well_jump pc len ofs;
      returnM b
  | CALL_IMM
  | RET_IMM =>
    do b <-- is_dst_R0 ins;
      returnM b
  | JMP_IMM_ILLEGAL_INS => returnM false
  end.

Definition bpf_verifier_opcode_branch_reg (pc len: nat) (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_branch_reg op with
  | JEQ_REG
  | JGT_REG
  | JGE_REG
  | JLT_REG
  | JLE_REG
  | JSET_REG
  | JNE_REG
  | JSGT_REG
  | JSGE_REG
  | JSLT_REG
  | JSLE_REG =>
    do ofs <-- get_offset ins;
    do b0 <-- is_well_src ins;
      if b0 then
        do b <-- is_well_jump pc len ofs;
          returnM b
      else
          returnM false
  | JMP_REG_ILLEGAL_INS => returnM false
  end.


Definition bpf_verifier_opcode_load_imm (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_load_imm op with
  | LDDW_low
  | LDDW_high => returnM true
  | LDX_IMM_ILLEGAL_INS => returnM false
  end.

Definition bpf_verifier_opcode_load_reg (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_load_reg op with
  | LDXW
  | LDXH
  | LDXB
  | LDXDW  =>
    do b <-- is_well_src ins;
      returnM b
  | LDX_REG_ILLEGAL_INS => returnM false
  end.

Definition bpf_verifier_opcode_store_imm (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_store_imm op with
  | STW
  | STH
  | STB
  | STDW  => returnM true
  | ST_ILLEGAL_INS => returnM false
  end.

Definition bpf_verifier_opcode_store_reg (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode_store_reg op with
  | STXW
  | STXH
  | STXB
  | STXDW  =>
    do b <-- is_well_src ins;
      returnM b
  | STX_ILLEGAL_INS => returnM false
  end.

Definition bpf_verifier_aux2 (pc len: nat) (op: nat8) (ins: int64_t) : M bool :=
  match nat_to_opcode op with
  | ALU64  (**r 0xX7 / 0xXf *) =>
    if Int.eq int32_0 (Int.and (nat2int op) int32_8) then
      do b <-- bpf_verifier_opcode_alu64_imm op ins;
      returnM b
    else
      do b <-- bpf_verifier_opcode_alu64_reg op ins;
      returnM b
  | ALU32  (**r 0xX4 / 0xXc *) =>
    if Int.eq int32_0 (Int.and (nat2int op) int32_8) then
      do b <-- bpf_verifier_opcode_alu32_imm op ins;
      returnM b
    else
      do b <-- bpf_verifier_opcode_alu32_reg op ins;
      returnM b
  | Branch (**r 0xX5 / 0xXd *) =>
    if Int.eq int32_0 (Int.and (nat2int op) int32_8) then
      do b <-- bpf_verifier_opcode_branch_imm pc len op ins;
      returnM b
    else
      do b <-- bpf_verifier_opcode_branch_reg pc len op ins;
      returnM b
  | LD_IMM (**r 0xX8 *)        => do b <-- bpf_verifier_opcode_load_imm op ins; returnM b
  | LD_REG (**r 0xX1/0xX9 *)   => do b <-- bpf_verifier_opcode_load_reg op ins; returnM b
  | ST_IMM (**r 0xX2/0xXa *)   => do b <-- bpf_verifier_opcode_store_imm op ins; returnM b
  | ST_REG (**r 0xX3/0xXb *)   => do b <-- bpf_verifier_opcode_store_reg op ins; returnM b
  | ILLEGAL => returnM false
  end.

Fixpoint bpf_verifier_aux (pc len: nat): M bool := (**r pc: len-1, len-2, ... 0 *)
    match pc with
    | O => returnM true
    | S n =>
      do ins <-- eval_ins (nat2int n); (**r len-pc: 0, 1, 2, etc... len -1 *)
      do b   <-- is_well_dst ins;
        if b then
          do op   <-- get_opcode ins;
          do b0    <-- bpf_verifier_aux2 n len op ins;
            if b0 then
              bpf_verifier_aux n len
            else
              returnM false
        else
          returnM false
    end.

Definition bpf_verifier: M bool :=
  do len  <-- eval_ins_len;
  (**r (0, Int.max_unsigned/8): at least one instruction, and at most Int.max_unsigned/8 because of memory region *)
    if Int_leu (int32_1) (nat2int len) then
      if Int_leu (nat2int len) (Int.divu int32_max_unsigned int32_8) then
        do b <-- bpf_verifier_aux len len;
          if b then
            do ins64 <-- eval_ins (nat2int (Nat.sub len nat32_1));
              returnM (Int64.eq ins64 int64_0x95)
          else
            returnM false
      else
        returnM false
    else
      returnM false.

Close Scope monad_scope.
Close Scope nat_scope.
