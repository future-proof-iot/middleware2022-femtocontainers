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

From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

From bpf.dxcomm Require Import InfComp GenMatchable CoqIntegers DxNat.
From bpf.verifier.synthesismodel Require Import opcode_synthesis.

(******************** Dx related *******************)

Open Scope Z_scope.

Definition opcodeCompilableType :=
  MkCompilableType opcode C_U8.

Definition opcodeCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcodeCompilableType  opcode_eqb
    (     (ALU64, 0x07)
       :: (ALU32, 0x04)
       :: (Branch, 0x05)
       :: (LD_IMM, 0x00)
       :: (LD_REG, 0x01)
       :: (ST_IMM, 0x02)
       :: (ST_REG, 0x03) :: nil)
    ILLEGAL
    (fun m A => opcode_rect (fun _ => m A))).

Instance CINT : CType nat := mkCType _ (cType nat8CompilableType).
Instance COP : CType opcode := mkCType _ (cType opcodeCompilableType).

Definition opcodeSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcodeCompilableType).

Definition Const_nat_to_opcode :=
  ltac: (mkprimitive nat_to_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_NAT8_0x07 C_U8) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_alu64_immCompilableType :=
  MkCompilableType opcode_alu64_imm C_U8.

Definition opcode_alu64_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu64_immCompilableType  opcode_alu64_imm_eqb
    (     (ADD64_IMM, 0x07)
       :: (SUB64_IMM, 0x17)
       :: (MUL64_IMM, 0x27)
       :: (DIV64_IMM, 0x37)
       :: (OR64_IMM,  0x47)
       :: (AND64_IMM, 0x57)
       :: (LSH64_IMM, 0x67)
       :: (RSH64_IMM, 0x77)
       :: (NEG64_IMM, 0x87)
       :: (MOD64_IMM, 0x97)
       :: (XOR64_IMM, 0xa7)
       :: (MOV64_IMM, 0xb7)
       :: (ARSH64_IMM, 0xc7) :: nil)
    ALU64_IMM_ILLEGAL
    (fun m A => opcode_alu64_imm_rect (fun _ => m A))).

Instance COP_alu64_imm : CType opcode_alu64_imm  := mkCType _ (cType opcode_alu64_immCompilableType).

Definition opcode_alu64_immSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_alu64_immCompilableType).

Definition Const_nat_to_opcode_alu64_imm :=
  ltac: (mkprimitive nat_to_opcode_alu64_imm
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_alu64_regCompilableType :=
  MkCompilableType opcode_alu64_reg C_U8.

Definition opcode_alu64_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu64_regCompilableType  opcode_alu64_reg_eqb
    (     (ADD64_REG, 0x0f)
       :: (SUB64_REG, 0x1f)
       :: (MUL64_REG, 0x2f)
       :: (DIV64_REG, 0x3f)
       :: (OR64_REG,  0x4f)
       :: (AND64_REG, 0x5f)
       :: (LSH64_REG, 0x6f)
       :: (RSH64_REG, 0x7f)
       :: (MOD64_REG, 0x9f)
       :: (XOR64_REG, 0xaf)
       :: (MOV64_REG, 0xbf)
       :: (ARSH64_REG, 0xcf) :: nil)
    ALU64_REG_ILLEGAL
    (fun m A => opcode_alu64_reg_rect (fun _ => m A))).

Instance COP_alu64_reg : CType opcode_alu64_reg  := mkCType _ (cType opcode_alu64_regCompilableType).

Definition opcode_alu64_regSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_alu64_regCompilableType).

Definition Const_nat_to_opcode_alu64_reg :=
  ltac: (mkprimitive nat_to_opcode_alu64_reg
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_alu32_immCompilableType :=
  MkCompilableType opcode_alu32_imm C_U8.

Definition opcode_alu32_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu32_immCompilableType  opcode_alu32_imm_eqb
    (     (ADD32_IMM, 0x04)
       :: (SUB32_IMM, 0x14)
       :: (MUL32_IMM, 0x24)
       :: (DIV32_IMM, 0x34)
       :: (OR32_IMM,  0x44)
       :: (AND32_IMM, 0x54)
       :: (LSH32_IMM, 0x64)
       :: (RSH32_IMM, 0x74)
       :: (NEG32_IMM, 0x84)
       :: (MOD32_IMM, 0x94)
       :: (XOR32_IMM, 0xa4)
       :: (MOV32_IMM, 0xb4)
       :: (ARSH32_IMM, 0xc4) :: nil)
    ALU32_IMM_ILLEGAL
    (fun m A => opcode_alu32_imm_rect (fun _ => m A))).

Instance COP_alu32_imm : CType opcode_alu32_imm  := mkCType _ (cType opcode_alu32_immCompilableType).

Definition opcode_alu32_immSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_alu32_immCompilableType).

Definition Const_nat_to_opcode_alu32_imm :=
  ltac: (mkprimitive nat_to_opcode_alu32_imm
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_alu32_regCompilableType :=
  MkCompilableType opcode_alu32_reg C_U8.

Definition opcode_alu32_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu32_regCompilableType  opcode_alu32_reg_eqb
    (     (ADD32_REG, 0x0c)
       :: (SUB32_REG, 0x1c)
       :: (MUL32_REG, 0x2c)
       :: (DIV32_REG, 0x3c)
       :: (OR32_REG,  0x4c)
       :: (AND32_REG, 0x5c)
       :: (LSH32_REG, 0x6c)
       :: (RSH32_REG, 0x7c)
       :: (MOD32_REG, 0x9c)
       :: (XOR32_REG, 0xac)
       :: (MOV32_REG, 0xbc)
       :: (ARSH32_REG, 0xcc) :: nil)
    ALU32_REG_ILLEGAL
    (fun m A => opcode_alu32_reg_rect (fun _ => m A))).

Instance COP_alu32_reg : CType opcode_alu32_reg  := mkCType _ (cType opcode_alu32_regCompilableType).

Definition opcode_alu32_regSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_alu32_regCompilableType).

Definition Const_nat_to_opcode_alu32_reg :=
  ltac: (mkprimitive nat_to_opcode_alu32_reg
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_branch_immCompilableType :=
  MkCompilableType opcode_branch_imm C_U8.

Definition opcode_branch_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_branch_immCompilableType  opcode_branch_imm_eqb
    (     (JA_IMM,  0x05)
       :: (JEQ_IMM, 0x15)
       :: (JGT_IMM, 0x25)
       :: (JGE_IMM, 0x35)
       :: (JLT_IMM, 0xa5)
       :: (JLE_IMM, 0xb5)
       :: (JNE_IMM, 0x45)
       :: (JNE_IMM, 0x55)
       :: (JSGT_IMM, 0x65)
       :: (JSGE_IMM, 0x75)
       :: (JSLT_IMM, 0xc5)
       :: (JSLE_IMM, 0xd5)
       :: (CALL_IMM, 0x85)
       :: (RET_IMM, 0x95) :: nil)
    JMP_IMM_ILLEGAL_INS
    (fun m A => opcode_branch_imm_rect (fun _ => m A))).

Instance COP_branch_imm : CType opcode_branch_imm  := mkCType _ (cType opcode_branch_immCompilableType).

Definition opcode_branch_immSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_branch_immCompilableType).

Definition Const_nat_to_opcode_branch_imm :=
  ltac: (mkprimitive nat_to_opcode_branch_imm
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_branch_regCompilableType :=
  MkCompilableType opcode_branch_reg C_U8.

Definition opcode_branch_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_branch_regCompilableType  opcode_branch_reg_eqb
    (     (JEQ_REG, 0x1d)
       :: (JGT_REG, 0x2d)
       :: (JGE_REG, 0x3d)
       :: (JLT_REG,  0xad)
       :: (JLE_REG, 0xbd)
       :: (JSET_REG, 0x4d)
       :: (JNE_REG, 0x5d)
       :: (JSGT_REG, 0x6d)
       :: (JSGE_REG, 0x7d)
       :: (JSLT_REG, 0xcd)
       :: (JSLE_REG, 0xdd) :: nil)
    JMP_REG_ILLEGAL_INS
    (fun m A => opcode_branch_reg_rect (fun _ => m A))).

Instance COP_branch_reg : CType opcode_branch_reg  := mkCType _ (cType opcode_branch_regCompilableType).

Definition opcode_branch_regSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_branch_regCompilableType).

Definition Const_nat_to_opcode_branch_reg :=
  ltac: (mkprimitive nat_to_opcode_branch_reg
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_load_immCompilableType :=
  MkCompilableType opcode_load_imm C_U8.

Definition opcode_load_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_load_immCompilableType  opcode_load_imm_eqb
    (     (LDDW_low,  0x18)
       :: (LDDW_high, 0x10) :: nil)
    LDX_IMM_ILLEGAL_INS
    (fun m A => opcode_load_imm_rect (fun _ => m A))).

Instance COP_load_imm : CType opcode_load_imm  := mkCType _ (cType opcode_load_immCompilableType).

Definition opcode_load_immSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_load_immCompilableType).

Definition Const_nat_to_opcode_load_imm :=
  ltac: (mkprimitive nat_to_opcode_load_imm
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_load_regCompilableType :=
  MkCompilableType opcode_load_reg C_U8.

Definition opcode_load_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_load_regCompilableType  opcode_load_reg_eqb
    (     (LDXW, 0x61)
       :: (LDXH, 0x69)
       :: (LDXB, 0x71)
       :: (LDXDW,  0x79) :: nil)
    LDX_REG_ILLEGAL_INS
    (fun m A => opcode_load_reg_rect (fun _ => m A))).

Instance COP_load_reg : CType opcode_load_reg  := mkCType _ (cType opcode_load_regCompilableType).

Definition opcode_load_regSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_load_regCompilableType).

Definition Const_nat_to_opcode_load_reg :=
  ltac: (mkprimitive nat_to_opcode_load_reg
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_store_immCompilableType :=
  MkCompilableType opcode_store_imm C_U8.

Definition opcode_store_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_store_immCompilableType  opcode_store_imm_eqb
    (     (STW,  0x62)
       :: (STH,  0x6a)
       :: (STB,  0x72)
       :: (STDW, 0x7a) :: nil)
    ST_ILLEGAL_INS
    (fun m A => opcode_store_imm_rect (fun _ => m A))).

Instance COP_store_imm : CType opcode_store_imm  := mkCType _ (cType opcode_store_immCompilableType).

Definition opcode_store_immSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_store_immCompilableType).

Definition Const_nat_to_opcode_store_imm :=
  ltac: (mkprimitive nat_to_opcode_store_imm
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition opcode_store_regCompilableType :=
  MkCompilableType opcode_store_reg C_U8.

Definition opcode_store_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_store_regCompilableType  opcode_store_reg_eqb
    (     (STXW,  0x63)
       :: (STXH,  0x6b)
       :: (STXB,  0x73)
       :: (STXDW, 0x7b) :: nil)
    STX_ILLEGAL_INS
    (fun m A => opcode_store_reg_rect (fun _ => m A))).

Instance COP_store_reg : CType opcode_store_reg  := mkCType _ (cType opcode_store_regCompilableType).

Definition opcode_store_regSymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some opcode_store_regCompilableType).

Definition Const_nat_to_opcode_store_reg :=
  ltac: (mkprimitive nat_to_opcode_store_reg
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end)).
Close Scope Z_scope.

Module Exports.
  Definition opcodeCompilableTypeMatchableType            := opcodeCompilableTypeMatchableType.
  Definition Const_nat_to_opcode                          := Const_nat_to_opcode.
  Definition opcode_alu64_immCompilableTypeMatchableType  := opcode_alu64_immCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_alu64_imm                := Const_nat_to_opcode_alu64_imm.
  Definition opcode_alu64_regCompilableTypeMatchableType  := opcode_alu64_regCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_alu64_reg                := Const_nat_to_opcode_alu64_reg.
  Definition opcode_alu32_immCompilableTypeMatchableType  := opcode_alu32_immCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_alu32_imm                := Const_nat_to_opcode_alu32_imm.
  Definition opcode_alu32_regCompilableTypeMatchableType  := opcode_alu32_regCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_alu32_reg                := Const_nat_to_opcode_alu32_reg.
  Definition opcode_branch_immCompilableTypeMatchableType := opcode_branch_immCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_branch_imm               := Const_nat_to_opcode_branch_imm.
  Definition opcode_branch_regCompilableTypeMatchableType := opcode_branch_regCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_branch_reg               := Const_nat_to_opcode_branch_reg.
  Definition opcode_load_immCompilableTypeMatchableType   := opcode_load_immCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_load_imm                 := Const_nat_to_opcode_load_imm.
  Definition opcode_load_regCompilableTypeMatchableType   := opcode_load_regCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_load_reg                 := Const_nat_to_opcode_load_reg.
  Definition opcode_store_immCompilableTypeMatchableType  := opcode_store_immCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_store_imm                := Const_nat_to_opcode_store_imm.
  Definition opcode_store_regCompilableTypeMatchableType  := opcode_store_regCompilableTypeMatchableType.
  Definition Const_nat_to_opcode_store_reg                := Const_nat_to_opcode_store_reg.
End Exports.