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

From bpf.comm Require Import Regs.
From bpf.dxcomm Require Import CoqIntegers DxIntegers DxValues.
From bpf.dxmodel Require Import IdentDef.

From Coq Require Import List ZArith.
Import ListNotations.

(******************** Dx Related *******************)

(** Coq2C: reg -> unsigned int;
           matchableType: R_i -> i,  i.e. R0 -> 0
  *)

Definition regCompilableType :=
  MkCompilableType reg C_U32.

Definition regSymbolType :=
  MkCompilableSymbolType nil (Some regCompilableType).

Definition Const_R0 := constant regSymbolType R0 C_U32_zero.

Definition Const_R1 := constant regSymbolType R1 C_U32_one.

Definition Const_R2 := constant regSymbolType R2 C_U32_2.

Definition Const_R3 := constant regSymbolType R3 C_U32_3.

Definition Const_R4 := constant regSymbolType R4 C_U32_4.

Definition Const_R5 := constant regSymbolType R5 C_U32_5.

Definition Const_R6 := constant regSymbolType R6 C_U32_6.

Definition Const_R7 := constant regSymbolType R7 C_U32_7.

Definition Const_R8 := constant regSymbolType R8 C_U32_8.

Definition Const_R9 := constant regSymbolType R9 C_U32_9.

Definition Const_R10 := constant regSymbolType R10 C_U32_10.

Close Scope Z_scope.


(** Coq2C: regmap -> unsigned long long int regmap[11];
  *)
Definition C_regmap: Ctypes.type := Ctypes.Tarray C_U64 11%Z Ctypes.noattr.

Definition regmapCompilableType := MkCompilableType regmap C_regmap.

(** Type signature: reg -> regmap -> val64
  *)
Definition regToregmapToVal64SymbolType :=
  MkCompilableSymbolType [regCompilableType; regmapCompilableType] (Some val64CompilableType).

Definition Const_eval_regmap :=
  MkPrimitive regToregmapToVal64SymbolType
                eval_regmap
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Eindex e2 e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: reg -> val64 -> regmap -> regmap
  *)
Definition regToval64ToregmapToregmapSymbolType :=
  MkCompilableSymbolType [regCompilableType; val64CompilableType; regmapCompilableType] (Some regmapCompilableType).

Definition Const_upd_regmap :=
  MkPrimitive regToval64ToregmapToregmapSymbolType
                upd_regmap
                (fun es => match es with
                           | [r; v; regmap] => Ok (
                              Csyntax.Eassign
                              (Csyntax.Eindex regmap r C_U64)
                              (Csyntax.Evalof v C_U64)
                              C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).



Module Exports.
  Definition regCompilableType      := regCompilableType.
  Definition Const_R0               := Const_R0.
  Definition Const_R1               := Const_R1.
  Definition Const_R2               := Const_R2.
  Definition Const_R3               := Const_R3.
  Definition Const_R4               := Const_R4.
  Definition Const_R5               := Const_R5.
  Definition Const_R6               := Const_R6.
  Definition Const_R7               := Const_R7.
  Definition Const_R8               := Const_R8.
  Definition Const_R9               := Const_R9.
  Definition Const_R10              := Const_R10.
  Definition regmapCompilableType   := regmapCompilableType.
  Definition Const_eval_regmap      := Const_eval_regmap.
  Definition Const_upd_regmap       := Const_upd_regmap.
End Exports.