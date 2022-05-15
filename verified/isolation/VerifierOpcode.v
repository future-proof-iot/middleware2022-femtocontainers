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

Inductive opcode_alu :=
  | ALU_DIV
  | ALU_SHIFT
  | ALU_IMM_Normal
  | ALU_REG_Normal
  | ALU_ILLEGAL.

Definition opcode_alu_eqb (x y: opcode_alu) :=
  match x, y with
  | ALU_DIV,  ALU_DIV
  | ALU_SHIFT,  ALU_SHIFT
  | ALU_IMM_Normal,  ALU_IMM_Normal
  | ALU_REG_Normal,  ALU_REG_Normal
  | ALU_ILLEGAL, ALU_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_alu (op: nat): opcode_alu :=
  match op with
  | 0x37 | 0x97 | 0x34 | 0x94 => ALU_DIV
  | 0x67 | 0x77 | 0xc7
  | 0x64 | 0x74 | 0xc4 => ALU_SHIFT
  | 0x07 | 0x17 | 0x27 | 0x47 | 0x57 | 0x87 | 0xa7 | 0xb7
  | 0x04 | 0x14 | 0x24 | 0x44 | 0x54 | 0x84 | 0xa4 | 0xb4 => ALU_IMM_Normal
  | 0x0f | 0x1f | 0x2f | 0x3f | 0x4f | 0x5f | 0x6f | 0x7f | 0x9f | 0xaf | 0xbf | 0xcf 
  | 0x0c | 0x1c | 0x2c | 0x3c | 0x4c | 0x5c | 0x6c | 0x7c | 0x9c | 0xac | 0xbc | 0xcc => ALU_REG_Normal
  | _    => ALU_ILLEGAL
  end.

Inductive opcode_branch :=
  | JMP_IMM
  | JMP_REG
  | JMP_SP
  | JMP_ILLEGAL.

Definition opcode_branch_eqb (x y: opcode_branch) :=
  match x, y with
  | JMP_IMM, JMP_IMM
  | JMP_REG, JMP_REG
  | JMP_SP,  JMP_SP
  | JMP_ILLEGAL, JMP_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_branch (op: nat): opcode_branch :=
  match op with
  | 0x05 | 0x15 | 0x25 | 0x35 | 0xa5 | 0xb5 | 0x45
  | 0x55 | 0x65 | 0x75 | 0xc5 | 0xd5 => JMP_IMM
  | 0x1d | 0x2d | 0x3d | 0xad | 0xbd | 0x4d
  | 0x5d | 0x6d | 0x7d | 0xcd | 0xdd => JMP_REG
  | 0x85 | 0x95 => JMP_SP
  | _    => JMP_ILLEGAL
  end.

Inductive opcode_load_imm :=
  | LD_IMM_Normal
  | LD_IMM_ILLEGAL.

Definition opcode_load_imm_eqb (x y: opcode_load_imm) :=
  match x, y with
  | LD_IMM_Normal, LD_IMM_Normal
  | LD_IMM_ILLEGAL,  LD_IMM_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_load_imm (op: nat): opcode_load_imm :=
  match op with
  | 0x18 | 0x10 => LD_IMM_Normal
  | _    => LD_IMM_ILLEGAL
  end.

Inductive opcode_load_reg :=
  | LD_REG_Normal
  | LD_REG_ILLEGAL.

Definition opcode_load_reg_eqb (x y: opcode_load_reg) :=
  match x, y with
  | LD_REG_Normal, LD_REG_Normal
  | LD_REG_ILLEGAL,  LD_REG_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_load_reg (op: nat): opcode_load_reg :=
  match op with
  | 0x61 | 0x69 | 0x71 | 0x79 => LD_REG_Normal
  | _ => LD_REG_ILLEGAL
  end.

Inductive opcode_store_imm :=
  | ST_IMM_Normal
  | ST_IMM_ILLEGAL.

Definition opcode_store_imm_eqb (x y: opcode_store_imm) :=
  match x, y with
  | ST_IMM_Normal, ST_IMM_Normal
  | ST_IMM_ILLEGAL,  ST_IMM_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_store_imm (op: nat): opcode_store_imm :=
  match op with
  | 0x62 | 0x6a | 0x72 | 0x7a => ST_IMM_Normal
  | _    => ST_IMM_ILLEGAL
  end.

Inductive opcode_store_reg :=
  | ST_REG_Normal
  | ST_REG_ILLEGAL.

Definition opcode_store_reg_eqb (x y: opcode_store_reg) :=
  match x, y with
  | ST_REG_Normal, ST_REG_Normal
  | ST_REG_ILLEGAL,  ST_REG_ILLEGAL => true
  | _, _ => false
  end.

Definition nat_to_opcode_store_reg (op: nat): opcode_store_reg :=
  match op with
  | 0x63 | 0x6b | 0x73 | 0x7b => ST_REG_Normal
  | _ => ST_REG_ILLEGAL
  end.