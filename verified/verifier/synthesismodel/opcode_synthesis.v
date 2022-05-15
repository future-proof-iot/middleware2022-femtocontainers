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

Inductive opcode :=
  | ALU64  (**r 0xX7 / 0xXf *)
  | ALU32  (**r 0xX4 / 0xXc *)
  | Branch (**r 0xX5 / 0xXd *)
  | LD_IMM (**r 0xX8 *)
  | LD_REG (**r 0xX1/0xX9 *)
  | ST_IMM (**r 0xX2/0xXa *)
  | ST_REG (**r 0xX3/0xXb *)
  | ILLEGAL.

Definition opcode_eqb (x y: opcode) :=
  match x, y with
  | ALU64,  ALU64
  | ALU32,  ALU32
  | Branch, Branch
  | LD_IMM, LD_IMM
  | LD_REG, LD_REG
  | ST_IMM, ST_IMM
  | ST_REG, ST_REG
  | ILLEGAL,ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode (op: nat): opcode :=
  let opc := Nat.land op 0x07 in (**r masking operation *)
    match opc with
    | 0x07 => ALU64
    | 0x04 => ALU32
    | 0x05 => Branch
    | 0x00 => LD_IMM
    | 0x01 => LD_REG
    | 0x02 => ST_IMM
    | 0x03 => ST_REG
    | _    => ILLEGAL
    end.

Inductive opcode_alu64_imm: Type := (**r 0xX7 *)
  (** ALU64_imm:13 *)
  | ADD64_IMM
  | SUB64_IMM
  | MUL64_IMM
  | DIV64_IMM
  | OR64_IMM
  | AND64_IMM
  | LSH64_IMM
  | RSH64_IMM
  | NEG64_IMM
  | MOD64_IMM
  | XOR64_IMM
  | MOV64_IMM
  | ARSH64_IMM
  | ALU64_IMM_ILLEGAL.

Definition opcode_alu64_imm_eqb (x y: opcode_alu64_imm) :=
  match x, y with
  | ADD64_IMM,  ADD64_IMM
  | SUB64_IMM,  SUB64_IMM
  | MUL64_IMM,  MUL64_IMM
  | DIV64_IMM,  DIV64_IMM
  | OR64_IMM,   OR64_IMM
  | AND64_IMM,  AND64_IMM
  | LSH64_IMM,  LSH64_IMM
  | RSH64_IMM,  RSH64_IMM
  | NEG64_IMM,  NEG64_IMM
  | MOD64_IMM,  MOD64_IMM
  | XOR64_IMM,  XOR64_IMM
  | MOV64_IMM,  MOV64_IMM
  | ARSH64_IMM, ARSH64_IMM
  | ALU64_IMM_ILLEGAL, ALU64_IMM_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_alu64_imm (op: nat): opcode_alu64_imm :=
    match op with
    | 0x07 => ADD64_IMM
    | 0x17 => SUB64_IMM
    | 0x27 => MUL64_IMM
    | 0x37 => DIV64_IMM
    | 0x47 => OR64_IMM
    | 0x57 => AND64_IMM
    | 0x67 => LSH64_IMM
    | 0x77 => RSH64_IMM
    | 0x87 => NEG64_IMM
    | 0x97 => MOD64_IMM
    | 0xa7 => XOR64_IMM
    | 0xb7 => MOV64_IMM
    | 0xc7 => ARSH64_IMM
    | _ => ALU64_IMM_ILLEGAL
    end.

Inductive opcode_alu64_reg: Type := (**r 0xXf *)
  (** ALU64_reg:13 *)
  | ADD64_REG
  | SUB64_REG
  | MUL64_REG
  | DIV64_REG
  | OR64_REG
  | AND64_REG
  | LSH64_REG
  | RSH64_REG
  | MOD64_REG
  | XOR64_REG
  | MOV64_REG
  | ARSH64_REG
  | ALU64_REG_ILLEGAL.

Definition opcode_alu64_reg_eqb (x y: opcode_alu64_reg) :=
  match x, y with
  | ADD64_REG,  ADD64_REG
  | SUB64_REG,  SUB64_REG
  | MUL64_REG,  MUL64_REG
  | DIV64_REG,  DIV64_REG
  | OR64_REG,   OR64_REG
  | AND64_REG,  AND64_REG
  | LSH64_REG,  LSH64_REG
  | RSH64_REG,  RSH64_REG
  | MOD64_REG,  MOD64_REG
  | XOR64_REG,  XOR64_REG
  | MOV64_REG,  MOV64_REG
  | ARSH64_REG, ARSH64_REG
  | ALU64_REG_ILLEGAL, ALU64_REG_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_alu64_reg (op: nat): opcode_alu64_reg :=
    match op with
    | 0x0f => ADD64_REG
    | 0x1f => SUB64_REG
    | 0x2f => MUL64_REG
    | 0x3f => DIV64_REG
    | 0x4f => OR64_REG
    | 0x5f => AND64_REG
    | 0x6f => LSH64_REG
    | 0x7f => RSH64_REG
    | 0x9f => MOD64_REG
    | 0xaf => XOR64_REG
    | 0xbf => MOV64_REG
    | 0xcf => ARSH64_REG
    | _ => ALU64_REG_ILLEGAL
    end.

Inductive opcode_alu32_imm: Type := (**r 0xX7 *)
  (** ALU32_imm:13 *)
  | ADD32_IMM
  | SUB32_IMM
  | MUL32_IMM
  | DIV32_IMM
  | OR32_IMM
  | AND32_IMM
  | LSH32_IMM
  | RSH32_IMM
  | NEG32_IMM
  | MOD32_IMM
  | XOR32_IMM
  | MOV32_IMM
  | ARSH32_IMM
  | ALU32_IMM_ILLEGAL.

Definition opcode_alu32_imm_eqb (x y: opcode_alu32_imm) :=
  match x, y with
  | ADD32_IMM,  ADD32_IMM
  | SUB32_IMM,  SUB32_IMM
  | MUL32_IMM,  MUL32_IMM
  | DIV32_IMM,  DIV32_IMM
  | OR32_IMM,   OR32_IMM
  | AND32_IMM,  AND32_IMM
  | LSH32_IMM,  LSH32_IMM
  | RSH32_IMM,  RSH32_IMM
  | NEG32_IMM,  NEG32_IMM
  | MOD32_IMM,  MOD32_IMM
  | XOR32_IMM,  XOR32_IMM
  | MOV32_IMM,  MOV32_IMM
  | ARSH32_IMM, ARSH32_IMM
  | ALU32_IMM_ILLEGAL, ALU32_IMM_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_alu32_imm (op: nat): opcode_alu32_imm :=
    match op with
    | 0x04 => ADD32_IMM
    | 0x14 => SUB32_IMM
    | 0x24 => MUL32_IMM
    | 0x34 => DIV32_IMM
    | 0x44 => OR32_IMM
    | 0x54 => AND32_IMM
    | 0x64 => LSH32_IMM
    | 0x74 => RSH32_IMM
    | 0x84 => NEG32_IMM
    | 0x94 => MOD32_IMM
    | 0xa4 => XOR32_IMM
    | 0xb4 => MOV32_IMM
    | 0xc4 => ARSH32_IMM
    | _ => ALU32_IMM_ILLEGAL
    end.

Inductive opcode_alu32_reg: Type := (**r 0xXf *)
  (** ALU32_reg:13 *)
  | ADD32_REG
  | SUB32_REG
  | MUL32_REG
  | DIV32_REG
  | OR32_REG
  | AND32_REG
  | LSH32_REG
  | RSH32_REG
  | MOD32_REG
  | XOR32_REG
  | MOV32_REG
  | ARSH32_REG
  | ALU32_REG_ILLEGAL.

Definition opcode_alu32_reg_eqb (x y: opcode_alu32_reg) :=
  match x, y with
  | ADD32_REG,  ADD32_REG
  | SUB32_REG,  SUB32_REG
  | MUL32_REG,  MUL32_REG
  | DIV32_REG,  DIV32_REG
  | OR32_REG,   OR32_REG
  | AND32_REG,  AND32_REG
  | LSH32_REG,  LSH32_REG
  | RSH32_REG,  RSH32_REG
  | MOD32_REG,  MOD32_REG
  | XOR32_REG,  XOR32_REG
  | MOV32_REG,  MOV32_REG
  | ARSH32_REG, ARSH32_REG
  | ALU32_REG_ILLEGAL, ALU32_REG_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_alu32_reg (op: nat): opcode_alu32_reg :=
    match op with
    | 0x0c => ADD32_REG
    | 0x1c => SUB32_REG
    | 0x2c => MUL32_REG
    | 0x3c => DIV32_REG
    | 0x4c => OR32_REG
    | 0x5c => AND32_REG
    | 0x6c => LSH32_REG
    | 0x7c => RSH32_REG
    | 0x9c => MOD32_REG
    | 0xac => XOR32_REG
    | 0xbc => MOV32_REG
    | 0xcc => ARSH32_REG
    | _ => ALU32_REG_ILLEGAL
    end.

Inductive opcode_branch_imm: Type := (**r 0xX5 *)
  (**Branch_imm: 13 *)
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
  | JSLE_IMM
  | CALL_IMM
  | RET_IMM
  | JMP_IMM_ILLEGAL_INS.

Definition opcode_branch_imm_eqb (x y: opcode_branch_imm) :=
  match x, y with
  | JA_IMM,   JA_IMM
  | JEQ_IMM,  JEQ_IMM
  | JGT_IMM,  JGT_IMM
  | JGE_IMM,  JGE_IMM
  | JLT_IMM,  JLT_IMM
  | JLE_IMM,  JLE_IMM
  | JSET_IMM, JSET_IMM
  | JNE_IMM,  JNE_IMM
  | JSGT_IMM, JSGT_IMM
  | JSGE_IMM, JSGE_IMM
  | JSLT_IMM, JSLT_IMM
  | JSLE_IMM, JSLE_IMM
  | CALL_IMM, CALL_IMM
  | RET_IMM,  RET_IMM
  | JMP_IMM_ILLEGAL_INS, JMP_IMM_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition nat_to_opcode_branch_imm (op: nat): opcode_branch_imm :=
    match op with
    | 0x05 => JA_IMM
    | 0x15 => JEQ_IMM
    | 0x25 => JGT_IMM
    | 0x35 => JGE_IMM
    | 0xa5 => JLT_IMM
    | 0xb5 => JLE_IMM
    | 0x45 => JSET_IMM
    | 0x55 => JNE_IMM
    | 0x65 => JSGT_IMM
    | 0x75 => JSGE_IMM
    | 0xc5 => JSLT_IMM
    | 0xd5 => JSLE_IMM
    | 0x85 => CALL_IMM
    | 0x95 => RET_IMM
    | _    => JMP_IMM_ILLEGAL_INS
    end.

Inductive opcode_branch_reg: Type := (**r 0xXd *)
  (**Branch_reg: 12 *)
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
  | JSLE_REG
  | JMP_REG_ILLEGAL_INS.

Definition opcode_branch_reg_eqb (x y: opcode_branch_reg) :=
  match x, y with
  | JEQ_REG,  JEQ_REG
  | JGT_REG,  JGT_REG
  | JGE_REG,  JGE_REG
  | JLT_REG,  JLT_REG
  | JLE_REG,  JLE_REG
  | JSET_REG, JSET_REG
  | JNE_REG,  JNE_REG
  | JSGT_REG, JSGT_REG
  | JSGE_REG, JSGE_REG
  | JSLT_REG, JSLT_REG
  | JSLE_REG, JSLE_REG
  | JMP_REG_ILLEGAL_INS, JMP_REG_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition nat_to_opcode_branch_reg (op: nat): opcode_branch_reg :=
    match op with
    | 0x1d => JEQ_REG
    | 0x2d => JGT_REG
    | 0x3d => JGE_REG
    | 0xad => JLT_REG
    | 0xbd => JLE_REG
    | 0x4d => JSET_REG
    | 0x5d => JNE_REG
    | 0x6d => JSGT_REG
    | 0x7d => JSGE_REG
    | 0xcd => JSLT_REG
    | 0xdd => JSLE_REG
    | _    => JMP_REG_ILLEGAL_INS
    end.

Inductive opcode_load_imm: Type :=  (**r 0xX8 *)
  (** Load/Store: 13 *)
  | LDDW_low
  | LDDW_high
  | LDX_IMM_ILLEGAL_INS.

Definition nat_to_opcode_load_imm (op: nat): opcode_load_imm :=
  match op with
  | 0x18 => LDDW_low
  | 0x10 => LDDW_high
  | _    => LDX_IMM_ILLEGAL_INS
  end.

Definition opcode_load_imm_eqb (x y: opcode_load_imm) :=
  match x, y with
  | LDDW_low,  LDDW_low
  | LDDW_high, LDDW_high
  | LDX_IMM_ILLEGAL_INS,  LDX_IMM_ILLEGAL_INS => true
  | _, _ => false
  end.

Inductive opcode_load_reg: Type :=  (**r 0xX1/0xX9 *)
  (** Load/Store: 13 *)
  | LDXW
  | LDXH
  | LDXB
  | LDXDW
  | LDX_REG_ILLEGAL_INS.

Definition nat_to_opcode_load_reg (op: nat): opcode_load_reg :=
  match op with
  | 0x61 => LDXW
  | 0x69 => LDXH
  | 0x71 => LDXB
  | 0x79 => LDXDW
  | _    => LDX_REG_ILLEGAL_INS
  end.

Definition opcode_load_reg_eqb (x y: opcode_load_reg) :=
  match x, y with
  | LDXW,  LDXW
  | LDXH,  LDXH
  | LDXB,  LDXB
  | LDXDW, LDXDW
  | LDX_REG_ILLEGAL_INS,  LDX_REG_ILLEGAL_INS => true
  | _, _ => false
  end.

Inductive opcode_store_imm: Type :=  (**r 0xX2/0xXa *)
  | STW
  | STH
  | STB
  | STDW
  | ST_ILLEGAL_INS.

Definition nat_to_opcode_store_imm (op: nat): opcode_store_imm :=
    match op with
    | 0x62 => STW
    | 0x6a => STH
    | 0x72 => STB
    | 0x7a => STDW
    | _    => ST_ILLEGAL_INS
    end.

Definition opcode_store_imm_eqb (x y: opcode_store_imm) :=
  match x, y with
  | STW,  STW
  | STH,  STH
  | STB,  STB
  | STDW, STDW
  | ST_ILLEGAL_INS,  ST_ILLEGAL_INS => true
  | _, _ => false
  end.

Inductive opcode_store_reg: Type :=  (**r 0xX3/0xXb *)
  | STXW
  | STXH
  | STXB
  | STXDW
  | STX_ILLEGAL_INS.

Definition nat_to_opcode_store_reg (op: nat): opcode_store_reg :=
  match op with
  | 0x63 => STXW
  | 0x6b => STXH
  | 0x73 => STXB
  | 0x7b => STXDW
  | _    => STX_ILLEGAL_INS
  end.

Definition opcode_store_reg_eqb (x y: opcode_store_reg) :=
  match x, y with
  | STXW,  STXW
  | STXH,  STXH
  | STXB,  STXB
  | STXDW, STXDW
  | STX_ILLEGAL_INS,  STX_ILLEGAL_INS => true
  | _, _ => false
  end.