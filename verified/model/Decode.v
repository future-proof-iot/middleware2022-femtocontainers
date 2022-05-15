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

From bpf.comm Require Import Flag Regs BinrBPF rBPFValues.
From bpf.model Require Import Syntax.

(** Overview:
    This module is used to translate `int64` binary code to bpf instructions~ Normally a bpf instruction has opcode+dst+src+offset+immedate.
  *)
Open Scope nat_scope.

Definition get_instruction_alu64_imm (ins: int64) (rd: reg) (i: int) (op: nat): instruction :=
  match op with
  (*ALU64_imm *)
  | 0x07 => BPF_BINARY A64 BPF_ADD  rd (inr i)
  | 0x17 => BPF_BINARY A64 BPF_SUB  rd (inr i)
  | 0x27 => BPF_BINARY A64 BPF_MUL  rd (inr i)
  | 0x37 => BPF_BINARY A64 BPF_DIV  rd (inr i)
  | 0x47 => BPF_BINARY A64 BPF_OR   rd (inr i)
  | 0x57 => BPF_BINARY A64 BPF_AND  rd (inr i)
  | 0x67 => BPF_BINARY A64 BPF_LSH  rd (inr i)
  | 0x77 => BPF_BINARY A64 BPF_RSH  rd (inr i)
  | 0x87 => BPF_NEG A64 rd
  | 0x97 => BPF_BINARY A64 BPF_MOD  rd (inr i)
  | 0xa7 => BPF_BINARY A64 BPF_XOR  rd (inr i)
  | 0xb7 => BPF_BINARY A64 BPF_MOV  rd (inr i)
  | 0xc7 => BPF_BINARY A64 BPF_ARSH rd (inr i)
  | _    => BPF_ERR
  end.

Definition get_instruction_alu64_reg (ins: int64) (rd rs: reg) (op: nat): instruction :=
  match op with
  (*ALU64_reg *)
  | 0x0f => BPF_BINARY A64 BPF_ADD  rd (inl rs)
  | 0x1f => BPF_BINARY A64 BPF_SUB  rd (inl rs)
  | 0x2f => BPF_BINARY A64 BPF_MUL  rd (inl rs)
  | 0x3f => BPF_BINARY A64 BPF_DIV  rd (inl rs)
  | 0x4f => BPF_BINARY A64 BPF_OR   rd (inl rs)
  | 0x5f => BPF_BINARY A64 BPF_AND  rd (inl rs)
  | 0x6f => BPF_BINARY A64 BPF_LSH  rd (inl rs)
  | 0x7f => BPF_BINARY A64 BPF_RSH  rd (inl rs)
  | 0x9f => BPF_BINARY A64 BPF_MOD  rd (inl rs)
  | 0xaf => BPF_BINARY A64 BPF_XOR  rd (inl rs)
  | 0xbf => BPF_BINARY A64 BPF_MOV  rd (inl rs)
  | 0xcf => BPF_BINARY A64 BPF_ARSH rd (inl rs)
  | _    => BPF_ERR
  end.


Definition get_instruction_alu32_imm (ins: int64) (rd: reg) (i: int) (op: nat): instruction :=
  match op with
  (* ALU32_imm *)
  | 0x04 => BPF_BINARY A32 BPF_ADD  rd (inr i)
  | 0x14 => BPF_BINARY A32 BPF_SUB  rd (inr i)
  | 0x24 => BPF_BINARY A32 BPF_MUL  rd (inr i)
  | 0x34 => BPF_BINARY A32 BPF_DIV  rd (inr i)
  | 0x44 => BPF_BINARY A32 BPF_OR   rd (inr i)
  | 0x54 => BPF_BINARY A32 BPF_AND  rd (inr i)
  | 0x64 => BPF_BINARY A32 BPF_LSH  rd (inr i)
  | 0x74 => BPF_BINARY A32 BPF_RSH  rd (inr i)
  | 0x84 => BPF_NEG A32 rd
  | 0x94 => BPF_BINARY A32 BPF_MOD  rd (inr i)
  | 0xa4 => BPF_BINARY A32 BPF_XOR  rd (inr i)
  | 0xb4 => BPF_BINARY A32 BPF_MOV  rd (inr i)
  | 0xc4 => BPF_BINARY A32 BPF_ARSH rd (inr i)
  | _    => BPF_ERR
  end.

Definition get_instruction_alu32_reg (ins: int64) (rd rs: reg) (op: nat): instruction :=
  match op with
  (*ALU32*)
  | 0x0c => BPF_BINARY A32 BPF_ADD  rd (inl rs)
  | 0x1c => BPF_BINARY A32 BPF_SUB  rd (inl rs)
  | 0x2c => BPF_BINARY A32 BPF_MUL  rd (inl rs)
  | 0x3c => BPF_BINARY A32 BPF_DIV  rd (inl rs)
  | 0x4c => BPF_BINARY A32 BPF_OR   rd (inl rs)
  | 0x5c => BPF_BINARY A32 BPF_AND  rd (inl rs)
  | 0x6c => BPF_BINARY A32 BPF_LSH  rd (inl rs)
  | 0x7c => BPF_BINARY A32 BPF_RSH  rd (inl rs)
  | 0x9c => BPF_BINARY A32 BPF_MOD  rd (inl rs)
  | 0xac => BPF_BINARY A32 BPF_XOR  rd (inl rs)
  | 0xbc => BPF_BINARY A32 BPF_MOV  rd (inl rs)
  | 0xcc => BPF_BINARY A32 BPF_ARSH rd (inl rs)
  | _    => BPF_ERR
  end.

Definition get_instruction_ld (ins: int64) (rd: reg) (i: int) (op: nat): instruction :=
  match Nat.land op 255 with
  | 0x18 => BPF_LDDW_low rd i
  | 0x10 => BPF_LDDW_high rd i
  | _    => BPF_ERR
  end.

Definition get_instruction_ldx (ins: int64) (rd rs: reg) (ofs: int) (op: nat): instruction :=
  match Nat.land op 255 with
  | 0x61 => BPF_LDX Mint32         rd rs ofs
  | 0x69 => BPF_LDX Mint16unsigned rd rs ofs
  | 0x71 => BPF_LDX Mint8unsigned  rd rs ofs
  | 0x79 => BPF_LDX Mint64         rd rs ofs
  | _    => BPF_ERR
  end.

Definition get_instruction_st (ins: int64) (rd: reg) (ofs: int) (i: int) (op: nat): instruction :=
  match Nat.land op 255 with
  | 0x62 => BPF_ST  Mint32         rd (inr i)  ofs
  | 0x6a => BPF_ST  Mint16unsigned rd (inr i)  ofs
  | 0x72 => BPF_ST  Mint8unsigned  rd (inr i)  ofs
  | 0x7a => BPF_ST  Mint64         rd (inr i)  ofs
  | _    => BPF_ERR
  end.

Definition get_instruction_stx (ins: int64) (rd rs: reg) (ofs: int) (op: nat): instruction :=
  match Nat.land op 255 with
  | 0x63 => BPF_ST  Mint32         rd (inl rs) ofs
  | 0x6b => BPF_ST  Mint16unsigned rd (inl rs) ofs
  | 0x73 => BPF_ST  Mint8unsigned  rd (inl rs) ofs
  | 0x7b => BPF_ST  Mint64         rd (inl rs) ofs
  | _    => BPF_ERR
  end.

Definition get_instruction_branch_imm (ins: int64) (rd: reg) (ofs: int) (i: int) (op: nat): instruction :=
  match op with
  | 0x05 => BPF_JA ofs
  | 0x15 => BPF_JUMP  Eq           rd (inr i)  ofs
  | 0x25 => BPF_JUMP (Gt Unsigned) rd (inr i)  ofs
  | 0x35 => BPF_JUMP (Ge Unsigned) rd (inr i)  ofs
  | 0xa5 => BPF_JUMP (Lt Unsigned) rd (inr i)  ofs
  | 0xb5 => BPF_JUMP (Le Unsigned) rd (inr i)  ofs
  | 0x45 => BPF_JUMP  SEt          rd (inr i)  ofs
  | 0x55 => BPF_JUMP  Ne           rd (inr i)  ofs
  | 0x65 => BPF_JUMP (Gt Signed)   rd (inr i)  ofs
  | 0x75 => BPF_JUMP (Ge Signed)   rd (inr i)  ofs
  | 0xc5 => BPF_JUMP (Lt Signed)   rd (inr i)  ofs
  | 0xd5 => BPF_JUMP (Le Signed)   rd (inr i)  ofs

  | 0x85 => BPF_CALL i
  | 0x95 => BPF_RET

  | _    => BPF_ERR
  end.

Definition get_instruction_branch_reg (ins: int64) (rd rs: reg) (ofs: int) (op: nat): instruction :=
  match op with
  | 0x1d => BPF_JUMP  Eq           rd (inl rs) ofs
  | 0x2d => BPF_JUMP (Gt Unsigned) rd (inl rs) ofs
  | 0x3d => BPF_JUMP (Ge Unsigned) rd (inl rs) ofs
  | 0xad => BPF_JUMP (Lt Unsigned) rd (inl rs) ofs
  | 0xbd => BPF_JUMP (Le Unsigned) rd (inl rs) ofs
  | 0x4d => BPF_JUMP  SEt          rd (inl rs) ofs
  | 0x5d => BPF_JUMP  Ne           rd (inl rs) ofs
  | 0x6d => BPF_JUMP (Gt Signed)   rd (inl rs) ofs
  | 0x7d => BPF_JUMP (Ge Signed)   rd (inl rs) ofs
  | 0xcd => BPF_JUMP (Lt Signed)   rd (inl rs) ofs
  | 0xdd => BPF_JUMP (Le Signed)   rd (inl rs) ofs
  | _    => BPF_ERR
  end.

Definition decode (ins: int64): option instruction :=
  let opcode := get_opcode ins in
    match int64_to_dst_reg' ins with
    | None => None
    | Some dst =>
      let opc := Nat.land opcode 0x07 in (**r masking operation *)
      let n_ofs    := get_offset ins in
      let n_imm    := get_immediate ins in
        match opc with
        | 0x07 => (* ALU64 *)
          if Int.eq Int.zero (Int.and (Int.repr (Z.of_nat opcode)) (Int.repr 8)) then
            Some (get_instruction_alu64_imm ins dst n_imm opcode)
          else
            match int64_to_src_reg' ins with
            | None => None
            | Some src => Some (get_instruction_alu64_reg ins dst src opcode)
            end
        | 0x04 => (* ALU32 *)
          if Int.eq Int.zero (Int.and (Int.repr (Z.of_nat opcode)) (Int.repr 8)) then
            Some (get_instruction_alu32_imm ins dst n_imm opcode)
          else
            match int64_to_src_reg' ins with
            | None => None
            | Some src => Some (get_instruction_alu32_reg ins dst src opcode)
            end
        | 0x05 => (* Branch *)
          if Int.eq Int.zero (Int.and (Int.repr (Z.of_nat opcode)) (Int.repr 8)) then
            Some (get_instruction_branch_imm ins dst n_ofs n_imm opcode)
          else
            match int64_to_src_reg' ins with
            | None => None
            | Some src => Some (get_instruction_branch_reg ins dst src n_ofs opcode)
            end
        | 0x00 => (* Mem_ld_imm *) Some (get_instruction_ld ins dst n_imm opcode)
        | 0x01 => (* Mem_ld_reg *)
          match int64_to_src_reg' ins with
          | None => None
          | Some src => Some (get_instruction_ldx ins dst src n_ofs opcode)
          end
        | 0x02 => (* Mem_st_imm *) Some (get_instruction_st ins dst n_ofs n_imm opcode)
        | 0x03 => (* Mem_st_reg *)
          match int64_to_src_reg' ins with
          | None => None
          | Some src => Some (get_instruction_stx ins dst src n_ofs opcode)
          end
        | _    => Some BPF_ERR
        end
    end.

Close Scope nat_scope.