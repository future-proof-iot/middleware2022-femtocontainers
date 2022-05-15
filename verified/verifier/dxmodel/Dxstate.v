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

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values Memory.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

From bpf.dxcomm Require Import CoqIntegers DxIntegers.
From bpf.verifier.comm Require Import state.

From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import IRtoC.
From Coq Require Import String.
Import UserIdentNotations.
Open Scope string.

Definition state_id:      AST.ident := $"verifier_state".
Definition ins_len_id:    AST.ident := $"ins_len".
Definition ins_id:        AST.ident := $"ins".
Close Scope string.

Definition state_struct_type: Ctypes.type := Ctypes.Tstruct state_id Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(ins_len_id, C_U32); (ins_id, C_U64_pointer)] Ctypes.noattr.

Definition stateCompilableType := MkCompilableType state state_struct_type.

Definition uint64ToboolSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some boolCompilableType).

Definition Const_is_dst_R0' :=
  MkPrimitive uint64ToboolSymbolType
                is_dst_R0'
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ebinop Cop.Oeq
                                          (Csyntax.Ecast (Csyntax.Ebinop Cop.Oshr
                                            (Csyntax.Ebinop Cop.Oand e1 C_U64_0xfff C_U64)
                                            C_U64_8 C_U64) C_U32)
                                           C_U32_zero C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_is_well_dst' :=
  MkPrimitive uint64ToboolSymbolType
                is_well_dst'
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ebinop Cop.Ole
                                          (Csyntax.Ecast (Csyntax.Ebinop Cop.Oshr
                                            (Csyntax.Ebinop Cop.Oand e1 C_U64_0xfff C_U64)
                                            C_U64_8 C_U64) C_U32)
                                           C_U32_10 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_is_well_src' :=
  MkPrimitive uint64ToboolSymbolType
                is_well_src'
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ebinop Cop.Ole
                                          (Csyntax.Ecast (Csyntax.Ebinop Cop.Oshr
                                            (Csyntax.Ebinop Cop.Oand e1 C_U64_0xffff C_U64)
                                            C_U64_12 C_U64) C_U32)
                                           C_U32_10 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition natTonatTointToboolSymbolType :=
  MkCompilableSymbolType [natCompilableType; natCompilableType; sint32CompilableType] (Some boolCompilableType).

Definition Const_is_well_jump' :=
  MkPrimitive natTonatTointToboolSymbolType
                is_well_jump'
                (fun es => match es with
                           | [e1; e2; e3] => Ok (Csyntax.Ebinop Cop.Ole
                                                  (Csyntax.Ebinop Cop.Oadd e1 e3 C_U32)
                                                  (Csyntax.Ebinop Cop.Osub e2 C_U32_2 C_U32) C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_is_not_div_by_zero' :=
  MkPrimitive uint64ToboolSymbolType
                is_not_div_by_zero'
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ebinop Cop.One
                                          (Csyntax.Ecast
                                            (Csyntax.Ebinop Cop.Oshr e1 C_U64_32 C_U64) C_S32)
                                           C_U32_zero C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_is_not_div_by_zero64' :=
  MkPrimitive uint64ToboolSymbolType
                is_not_div_by_zero64'
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ebinop Cop.One
                                          (Csyntax.Ecast
                                            (Csyntax.Ecast
                                              (Csyntax.Ebinop Cop.Oshr e1 C_U64_32 C_U64) C_S32) C_S64)
                                           C_U64_zero C_S64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition uint64Touint32ToboolSymbolType :=
  MkCompilableSymbolType [int64CompilableType; uint32CompilableType] (Some boolCompilableType).

Definition Const_is_shift_range' :=
  MkPrimitive uint64Touint32ToboolSymbolType
                is_shift_range'
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Olt
                                              (Csyntax.Ecast
                                                (Csyntax.Ebinop Cop.Oshr e1 C_U64_32 C_U64) C_S32)
                                              e2 C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_is_shift_range64' :=
  MkPrimitive uint64Touint32ToboolSymbolType
                is_shift_range64'
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Olt
                                              (Csyntax.Ecast
                                                (Csyntax.Ecast
                                                  (Csyntax.Ecast
                                                    (Csyntax.Ebinop Cop.Oshr e1 C_U64_32 C_U64) C_S32) C_U64) C_U32)
                                              e2 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition natTonatTouint32_aluSymbolType :=
  MkCompilableSymbolType [natCompilableType; natCompilableType] (Some uint32CompilableType).

Definition Const_nat2int2 :=
  MkPrimitive natTonatTouint32_aluSymbolType
                nat2int2
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Osub
                                              (Csyntax.Ebinop Cop.Osub e1 C_U32_one C_U32) e2 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition stateCompilableType            := stateCompilableType.
  Definition Const_is_dst_R0'               := Const_is_dst_R0'.
  Definition Const_is_well_dst'             := Const_is_well_dst'.
  Definition Const_is_well_src'             := Const_is_well_src'.
  Definition Const_is_well_jump'            := Const_is_well_jump'.
  Definition Const_is_not_div_by_zero'      := Const_is_not_div_by_zero'.
  Definition Const_is_not_div_by_zero64'    := Const_is_not_div_by_zero64'.
  Definition Const_is_shift_range'          := Const_is_shift_range'.
  Definition Const_is_shift_range64'        := Const_is_shift_range64'.
  Definition Const_nat2int2                 := Const_nat2int2.
End Exports.