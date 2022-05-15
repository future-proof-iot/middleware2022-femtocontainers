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

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool.

From bpf.comm Require Import rBPFValues.
From bpf.dxcomm Require Import InfComp CoqIntegers.
(*
(******************** UInt8 *******************)
Definition int8_t := byte.

(** masking operation *)
Definition int8_0xf0 := Byte.repr 0xf0.
Definition int8_0x07 := Byte.repr 0x07.
Definition int8_0xff := Byte.repr 0xff.
Definition int8_0x08 := Byte.repr 0x08.
Definition int8_zero := Byte.zero. *)
(*
(******************** UInt16 *******************)
Definition uint16_t := int16.

(******************** SInt16 *******************)

Definition sint16_t := int16. *)

(******************** UInt32 *******************)
Definition uint32_t := int.

Definition int32_0  := Int.zero.
Definition int32_1  := Int.one.
Definition int32_2  := Int.repr 2.
Definition int32_3  := Int.repr 3.
Definition int32_4  := Int.repr 4.
Definition int32_5  := Int.repr 5.
Definition int32_6  := Int.repr 6.
Definition int32_7  := Int.repr 7.
Definition int32_8  := Int.repr 8.
Definition int32_9  := Int.repr 9.
Definition int32_10 := Int.repr 10.

Definition int32_16 := Int.repr 16.
Definition int32_32 := Int.repr 32.
Definition int32_64 := Int.repr 64.
Definition int32_max_unsigned := Int.repr Int.max_unsigned.

(** masking operations *)
Definition int32_0xf0 := Int.repr 0xf0.
Definition int32_0x07 := Int.repr 0x07.
Definition int32_0xff := Int.repr 0xff.
Definition int32_0x08 := Int.repr 0x08.

(******************** SInt32 *******************)
Definition sint32_t := int. (**r here we should define two types for C: sint32_t and uint32_t, then we should use those two types to define rbpf functions *)

Definition sint32_0  := Int.zero.
Definition sint32_1  := Int.one.
Definition sint32_2  := Int.repr 2.
Definition sint32_3  := Int.repr 3.
Definition sint32_4  := Int.repr 4.
Definition sint32_5  := Int.repr 5.
Definition sint32_6  := Int.repr 6.
Definition sint32_7  := Int.repr 7.
Definition sint32_8  := Int.repr 8.
Definition sint32_9  := Int.repr 9.
Definition sint32_10 := Int.repr 10.

Definition int32_m2  := Int.repr (-2).
Definition int32_m3  := Int.repr (-3).
Definition int32_m4  := Int.repr (-4).
Definition int32_m5  := Int.repr (-5).
Definition int32_m6  := Int.repr (-6).
Definition int32_m7  := Int.repr (-7).
Definition int32_m8  := Int.repr (-8).
Definition int32_m9  := Int.repr (-9).
Definition int32_m10 := Int.repr (-10).
Definition int32_m11 := Int.repr (-11).
Definition int32_m12 := Int.repr (-12).

(******************** Int64 *******************)
Definition int64_t := int64.

Definition int64_2 := Int64.repr 2.

Definition int64_64 := Int64.repr 64.

Definition int64_0xff   := Int64.repr 0xff.
Definition int64_8      := Int64.repr 8.
Definition int64_12     := Int64.repr 12.
Definition int64_32     := Int64.repr 32.
Definition int64_48     := Int64.repr 48.
Definition int64_0x95   := Int64.repr 0x95.
Definition int64_0xfff  := Int64.repr 0xfff.
Definition int64_0xffff := Int64.repr 0xffff.

(** masking operation *)
Definition int64_0xf    := Int64.repr 0xf.

(******************** Int64 Type Casting *******************)

(******************** Dx Related *******************)


(******************** UInt8 *******************)

(******************** UInt16 *******************)

(******************** UInt32 *******************)

Definition C_U32_zero: Csyntax.expr :=
  Csyntax.Eval (Vint int32_0) C_U32.

Definition C_U32_one: Csyntax.expr :=
  Csyntax.Eval (Vint int32_1) C_U32.

Definition C_U32_2: Csyntax.expr :=
  Csyntax.Eval (Vint int32_2) C_U32.

Definition C_U32_3: Csyntax.expr :=
  Csyntax.Eval (Vint int32_3) C_U32.

Definition C_U32_4: Csyntax.expr :=
  Csyntax.Eval (Vint int32_4) C_U32.

Definition C_U32_5: Csyntax.expr :=
  Csyntax.Eval (Vint int32_5) C_U32.

Definition C_U32_6: Csyntax.expr :=
  Csyntax.Eval (Vint int32_6) C_U32.

Definition C_U32_7: Csyntax.expr :=
  Csyntax.Eval (Vint int32_7) C_U32.

Definition C_U32_8: Csyntax.expr :=
  Csyntax.Eval (Vint int32_8) C_U32.

Definition C_U32_9: Csyntax.expr :=
  Csyntax.Eval (Vint int32_9) C_U32.

Definition C_U32_10: Csyntax.expr :=
  Csyntax.Eval (Vint int32_10) C_U32.

Definition C_U32_16: Csyntax.expr :=
  Csyntax.Eval (Vint int32_16) C_U32.

Definition C_U32_32: Csyntax.expr :=
  Csyntax.Eval (Vint int32_32) C_U32.

Definition C_U32_64: Csyntax.expr :=
  Csyntax.Eval (Vint int32_64) C_U32.

Definition C_U32_max_unsigned: Csyntax.expr :=
  Csyntax.Eval (Vint int32_max_unsigned) C_U32.

(**r masking operations *)
Definition C_U32_0xf0: Csyntax.expr :=
  Csyntax.Eval (Vint int32_0xf0) C_U32.

Definition C_U32_0x07: Csyntax.expr :=
  Csyntax.Eval (Vint int32_0x07) C_U32.

Definition C_U32_0xff: Csyntax.expr :=
  Csyntax.Eval (Vint int32_0xff) C_U32.

Definition C_U32_0x08: Csyntax.expr :=
  Csyntax.Eval (Vint int32_0x08) C_U32.

Definition uint32CompilableType :=
  MkCompilableType uint32_t C_U32.

Definition uint32SymbolType :=
  MkCompilableSymbolType nil (Some uint32CompilableType).

Definition Const_uint32_zero := constant uint32SymbolType int32_0 C_U32_zero.

Definition Const_uint32_one := constant uint32SymbolType int32_1 C_U32_one.

Definition Const_uint32_2 := constant uint32SymbolType int32_2 C_U32_2.

Definition Const_uint32_3 := constant uint32SymbolType int32_3 C_U32_3.

Definition Const_uint32_4 := constant uint32SymbolType int32_4 C_U32_4.

Definition Const_uint32_5 := constant uint32SymbolType int32_5 C_U32_5.

Definition Const_uint32_6 := constant uint32SymbolType int32_6 C_U32_6.

Definition Const_uint32_7 := constant uint32SymbolType int32_7 C_U32_7.

Definition Const_uint32_8 := constant uint32SymbolType int32_8 C_U32_8.

Definition Const_uint32_9 := constant uint32SymbolType int32_9 C_U32_9.

Definition Const_uint32_10 := constant uint32SymbolType int32_10 C_U32_10.

Definition Const_uint32_16 := constant uint32SymbolType int32_16 C_U32_16.

Definition Const_uint32_32 := constant uint32SymbolType int32_32 C_U32_32.

Definition Const_uint32_64 := constant uint32SymbolType int32_64 C_U32_64.

Definition Const_uint32_max_unsigned := constant uint32SymbolType int32_max_unsigned C_U32_max_unsigned.

Definition Const_int32_0xf0 := constant uint32SymbolType int32_0xf0 C_U32_0xf0.
Definition Const_int32_0x07 := constant uint32SymbolType int32_0x07 C_U32_0x07.
Definition Const_int32_0xff := constant uint32SymbolType int32_0xff C_U32_0xff.
Definition Const_int32_0x08 := constant uint32SymbolType int32_0x08 C_U32_0x08.

Definition uint32Touint32SymbolType :=
  MkCompilableSymbolType [uint32CompilableType] (Some uint32CompilableType).

Definition Const_uint32_neg :=
  MkPrimitive uint32Touint32SymbolType
                Int.neg
                (fun es => match es with
                           | [e1] => Ok (C_U32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition uint32Touint32ToboolSymbolType :=
  MkCompilableSymbolType [uint32CompilableType; uint32CompilableType] (Some boolCompilableType).

Definition C_int32_eq (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oeq x y C_U32.

Definition Const_int32_eq :=
  MkPrimitive uint32Touint32ToboolSymbolType
                Int.eq
                (fun es => match es with
                           | [e1;e2] => Ok (C_int32_eq e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_uint32_ltu :=
  MkPrimitive uint32Touint32ToboolSymbolType
                Int.ltu
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Olt e1 e2 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_uint32_leu :=
  MkPrimitive uint32Touint32ToboolSymbolType
                Int_leu
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Ole e1 e2 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).


Definition uint32Touint32Touint32SymbolType :=
  MkCompilableSymbolType [uint32CompilableType; uint32CompilableType] (Some uint32CompilableType).

Definition binop_expr (op: Cop.binary_operation) (ti : Ctypes.type) :=
  fun es => match es with
            | [e1;e2] => Ok (Csyntax.Ebinop op e1 e2 ti)
            |  _      => Err PrimitiveEncodingFailed
            end.

Definition binop_expr_cast1 (op: Cop.binary_operation) (t ti : Ctypes.type) :=
  fun es => match es with
            | [e1;e2] => Ok (Csyntax.Ecast (Csyntax.Ebinop op (Csyntax.Ecast e1 t) e2 ti) ti)
            |  _      => Err PrimitiveEncodingFailed
            end.

Definition binop_expr_cast2 (op: Cop.binary_operation) (t ti : Ctypes.type) :=
  fun es => match es with
            | [e1;e2] => Ok (Csyntax.Ebinop op (Csyntax.Ecast e1 t) (Csyntax.Ecast e2 t) ti)
            |  _      => Err PrimitiveEncodingFailed
            end.

Instance CUINT32 : CType uint32_t := mkCType _ (cType uint32CompilableType).

Definition Const_uint32_add := ltac: (mkprimitive Int.add (binop_expr Cop.Oadd C_U32)).
Definition Const_uint32_sub := ltac: (mkprimitive Int.sub (binop_expr Cop.Osub C_U32)).
Definition Const_uint32_div := ltac: (mkprimitive Int.divu (binop_expr Cop.Odiv C_U32)).
Definition Const_uint32_and := ltac: (mkprimitive Int.and (binop_expr Cop.Oand C_U32)).

(******************** SInt32 *******************)
Definition C_S32_zero: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_0) C_S32.

Definition C_S32_one: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_1) C_S32.

Definition C_S32_2: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_2) C_S32.

Definition C_S32_3: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_3) C_S32.

Definition C_S32_4: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_4) C_S32.

Definition C_S32_5: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_5) C_S32.

Definition C_S32_6: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_6) C_S32.

Definition C_S32_7: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_7) C_S32.

Definition C_S32_8: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_8) C_S32.

Definition C_S32_9: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_9) C_S32.

Definition C_S32_10: Csyntax.expr :=
  Csyntax.Eval (Vint sint32_10) C_S32.

Definition C_S32_32: Csyntax.expr :=
  Csyntax.Eval (Vint int32_32) C_S32.

Definition C_S32_mone: Csyntax.expr :=
  Csyntax.Eval (Vint Int.mone) C_S32.

Definition C_S32_m2: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m2) C_S32.

Definition C_S32_m3: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m3) C_S32.

Definition C_S32_m4: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m4) C_S32.

Definition C_S32_m5: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m5) C_S32.

Definition C_S32_m6: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m6) C_S32.

Definition C_S32_m7: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m7) C_S32.

Definition C_S32_m8: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m8) C_S32.

Definition C_S32_m9: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m9) C_S32.

Definition C_S32_m10: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m10) C_S32.

Definition C_S32_m11: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m11) C_S32.

Definition C_S32_m12: Csyntax.expr :=
  Csyntax.Eval (Vint int32_m12) C_S32.

Definition C_S32_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_S32.

Definition C_S32_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_S32.

Definition C_S32_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_S32.

Definition sint32CompilableType :=
  MkCompilableType sint32_t C_S32.

Definition sint32SymbolType :=
  MkCompilableSymbolType nil (Some sint32CompilableType).

Definition Const_sint32_zero := constant sint32SymbolType sint32_0 C_S32_zero.

Definition Const_sint32_one := constant sint32SymbolType sint32_1 C_S32_one.

Definition Const_sint32_2 := constant sint32SymbolType sint32_2 C_S32_2.

Definition Const_sint32_3 := constant sint32SymbolType sint32_3 C_S32_3.

Definition Const_sint32_4 := constant sint32SymbolType sint32_4 C_S32_4.

Definition Const_sint32_5 := constant sint32SymbolType sint32_5 C_S32_5.

Definition Const_sint32_6 := constant sint32SymbolType sint32_6 C_S32_6.

Definition Const_sint32_7 := constant sint32SymbolType sint32_7 C_S32_7.

Definition Const_sint32_8 := constant sint32SymbolType sint32_8 C_S32_8.

Definition Const_sint32_9 := constant sint32SymbolType sint32_9 C_S32_9.

Definition Const_sint32_10 := constant sint32SymbolType sint32_10 C_S32_10.

Definition Const_sint32_mone := constant sint32SymbolType Int.mone C_S32_mone.

Definition Const_sint32_m2 := constant sint32SymbolType int32_m2 C_S32_m2.

Definition Const_sint32_m3 := constant sint32SymbolType int32_m3 C_S32_m3.

Definition Const_sint32_m4 := constant sint32SymbolType int32_m4 C_S32_m4.

Definition Const_sint32_m5 := constant sint32SymbolType int32_m5 C_S32_m5.

Definition Const_sint32_m6 := constant sint32SymbolType int32_m6 C_S32_m6.

Definition Const_sint32_m7 := constant sint32SymbolType int32_m7 C_S32_m7.

Definition Const_sint32_m8 := constant sint32SymbolType int32_m8 C_S32_m8.

Definition Const_sint32_m9 := constant sint32SymbolType int32_m9 C_S32_m9.

Definition Const_sint32_m10 := constant sint32SymbolType int32_m10 C_S32_m10.

Definition Const_sint32_m11 := constant sint32SymbolType int32_m11 C_S32_m11.

Definition Const_sint32_m12 := constant sint32SymbolType int32_m12 C_S32_m12.

Definition sint32Tosint32SymbolType :=
  MkCompilableSymbolType [sint32CompilableType] (Some sint32CompilableType).

Definition Const_sint32_neg :=
  MkPrimitive sint32Tosint32SymbolType
                Int.neg
                (fun es => match es with
                           | [e1] => Ok (C_S32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition sint32Tosint32Tosint32SymbolType :=
  MkCompilableSymbolType [sint32CompilableType; sint32CompilableType] (Some sint32CompilableType).

Definition Const_sint32_add :=
  MkPrimitive sint32Tosint32Tosint32SymbolType
                Int.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_S32_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_sint32_sub :=
  MkPrimitive sint32Tosint32Tosint32SymbolType
                Int.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_S32_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: sint32 -> sint32 -> bool
  *)
Definition sint32Tosint32ToboolSymbolType :=
  MkCompilableSymbolType [sint32CompilableType; sint32CompilableType] (Some boolCompilableType).

Definition Const_sint32_lt :=
  MkPrimitive sint32Tosint32ToboolSymbolType
                Int.lt
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Olt e1 e2 C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).
(*
Definition Int_le (x y: int): bool := negb (Int.lt y x). *)

Definition Const_sint32_le :=
  MkPrimitive sint32Tosint32ToboolSymbolType
                Int_le
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Ole e1 e2 C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition sint32Touint32SymbolType :=
  MkCompilableSymbolType [sint32CompilableType] (Some uint32CompilableType).

Definition Const_sint32_to_uint32 :=
  MkPrimitive sint32Touint32SymbolType
                sint32_to_uint32
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).
(*
Definition sint16Tosint32SymbolType :=
  MkCompilableSymbolType [sint16CompilableType] (Some sint32CompilableType).

Definition Const_sint16_to_sint32 :=
  MkPrimitive sint16Tosint32SymbolType
                sint16_to_sint32
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).*)


(******************** Int64 *******************)
Definition int64CompilableType :=
  MkCompilableType int64_t C_U64.

Definition int64SymbolType :=
  MkCompilableSymbolType nil (Some int64CompilableType).

Definition C_U64_zero: Csyntax.expr :=
  Csyntax.Eval (Vlong Int64.zero) C_U64.

Definition C_U64_one: Csyntax.expr :=
  Csyntax.Eval (Vlong Int64.one) C_U64.

Definition C_U64_2: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_2) C_U64.

Definition C_U64_64: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_64) C_U64.


Definition C_U64_0xff: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_0xff) C_U64.
Definition C_U64_8:  Csyntax.expr :=
  Csyntax.Eval (Vlong int64_8) C_U64.
Definition C_U64_12: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_12) C_U64.
Definition C_U64_32: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_32) C_U64.
Definition C_U64_48: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_48) C_U64.
Definition C_U64_0x95: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_0x95) C_U64.
Definition C_U64_0xfff: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_0xfff) C_U64.
Definition C_U64_0xffff: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_0xffff) C_U64.

(** masking operation*)
Definition C_U64_0xf: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_0xf) C_U64.
(*
Definition C_U64_max_unsigned: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr (Int64.max_unsigned))) C_U64.*)

Definition Const_int64_0xff := constant int64SymbolType int64_0xff C_U64_0xff.
Definition Const_int64_8  := constant int64SymbolType int64_8  C_U64_8.
Definition Const_int64_12 := constant int64SymbolType int64_12 C_U64_12.
Definition Const_int64_32 := constant int64SymbolType int64_32 C_U64_32.
Definition Const_int64_48 := constant int64SymbolType int64_48 C_U64_48.
Definition Const_int64_0x95 := constant int64SymbolType int64_0x95 C_U64_0x95.
Definition Const_int64_0xfff := constant int64SymbolType int64_0xfff C_U64_0xfff.
Definition Const_int64_0xffff := constant int64SymbolType int64_0xffff C_U64_0xffff.

(** masking operation*)
Definition Const_int64_0xf := constant int64SymbolType int64_0xf C_U64_0xf.
(*
Definition Const_int64_max_unsigned := constant int64SymbolType int64_max_unsigned C_U64_max_unsigned.*)

Definition Const_int64_zero := constant int64SymbolType Int64.zero C_U64_zero.

Definition Const_int64_one := constant int64SymbolType Int64.one C_U64_one.

Definition Const_int64_2 := constant int64SymbolType int64_2 C_U64_2.

Definition Const_int64_64 := constant int64SymbolType int64_64 C_U64_64.

Definition int64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some int64CompilableType).

Definition Const_int64_neg :=
  MkPrimitive int64Toint64SymbolType
                Int64.neg
                (fun es => match es with
                           | [e1] => Ok (C_U64_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition int64Toint64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType; int64CompilableType] (Some int64CompilableType).

Definition Const_int64_add :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_sub :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_and :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.and
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_and e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_shr :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.shr
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_shr (Csyntax.Ecast  e1 C_S64) e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_shru :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.shru
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_shr e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_shl :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.shl
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_shl e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).
(** Type signature: int64 -> int64 -> bool
  *)
Definition int64Toint64ToboolSymbolType :=
  MkCompilableSymbolType [int64CompilableType; int64CompilableType] (Some boolCompilableType).

Definition Const_int64_eq :=
  MkPrimitive int64Toint64ToboolSymbolType
                Int64.eq
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Oeq e1 e2 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_lt :=
  MkPrimitive int64Toint64ToboolSymbolType
                Int64.lt
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Olt (Csyntax.Ecast e1 C_S64) (Csyntax.Ecast e2 C_S64) C_S64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_ltu :=
  MkPrimitive int64Toint64ToboolSymbolType
                Int64.ltu
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.Olt e1 e2 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Int64 Type Casting *******************)
(*
Definition int16Toint8SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some int8CompilableType).

Definition Const_int64_to_int8 :=
  MkPrimitive int16Toint8SymbolType
                int64_to_int8
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end). *)
(*
Definition sint16Toint64SymbolType :=
  MkCompilableSymbolType [sint16CompilableType] (Some int64CompilableType).

Definition Const_sint16_to_int64 :=
  MkPrimitive sint16Toint64SymbolType
                sint16_to_int64
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition int64Tosint16SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some sint16CompilableType).

Definition Const_int64_to_sint16 :=
  MkPrimitive int64Tosint16SymbolType
                int64_to_sint16
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_S16)
                           | _       => Err PrimitiveEncodingFailed
                           end).*)

Definition int64Tosint32SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some sint32CompilableType).

Definition Const_int64_to_sint32 :=
  MkPrimitive int64Tosint32SymbolType
                int64_to_sint32
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports. (*
  Definition int8CompilableType    := int8CompilableType.

  (** masking operation *)
  Definition Const_int8_0xf0       := Const_int8_0xf0.
  Definition Const_int8_0x07       := Const_int8_0x07.
  Definition Const_int8_0xff       := Const_int8_0xff.
  Definition Const_int8_0x08       := Const_int8_0x08.
  Definition Const_int8_eq         := Const_int8_eq.
  Definition Const_int8_and        := Const_int8_and.
  Definition Const_int8_zero       := Const_int8_zero. *)
(*
  Definition uint16CompilableType  := uint16CompilableType.
  Definition Const_uint16_zero     := Const_uint16_zero.
  Definition Const_uint16_one      := Const_uint16_one.
  Definition Const_uint16_add      := Const_uint16_add.
  Definition Const_uint16_sub      := Const_uint16_sub.
  Definition sint16CompilableType  := sint16CompilableType.
  Definition Const_sint16_zero     := Const_sint16_zero.
  Definition Const_sint16_one      := Const_sint16_one.
  Definition Const_sint16_add      := Const_sint16_add.
  Definition Const_sint16_sub      := Const_sint16_sub.*)
  Definition uint32CompilableType  := uint32CompilableType.
  Definition Const_uint32_zero     := Const_uint32_zero.
  Definition Const_uint32_one      := Const_uint32_one.
  Definition Const_uint32_2        := Const_uint32_2.
  Definition Const_uint32_3        := Const_uint32_3.
  Definition Const_uint32_4        := Const_uint32_4.
  Definition Const_uint32_5        := Const_uint32_5.
  Definition Const_uint32_6        := Const_uint32_6.
  Definition Const_uint32_7        := Const_uint32_7.
  Definition Const_uint32_8        := Const_uint32_8.
  Definition Const_uint32_9        := Const_uint32_9.
  Definition Const_uint32_10       := Const_uint32_10.
  Definition Const_uint32_16       := Const_uint32_16.
  Definition Const_uint32_32       := Const_uint32_32.
  Definition Const_uint32_64       := Const_uint32_64.
  Definition Const_uint32_max_unsigned := Const_uint32_max_unsigned.
  Definition Const_int32_0xf0       := Const_int32_0xf0.
  Definition Const_int32_0x07       := Const_int32_0x07.
  Definition Const_int32_0xff       := Const_int32_0xff.
  Definition Const_int32_0x08       := Const_int32_0x08.

  Definition Const_uint32_neg      := Const_uint32_neg.
  Definition Const_int32_eq        := Const_int32_eq.
  Definition Const_uint32_ltu      := Const_uint32_ltu.
  Definition Const_uint32_leu      := Const_uint32_leu.
  Definition Const_uint32_add      := Const_uint32_add.
  Definition Const_uint32_sub      := Const_uint32_sub.
  Definition Const_uint32_div      := Const_uint32_div.
  Definition Const_uint32_and      := Const_uint32_and.
  Definition sint32CompilableType  := sint32CompilableType.
  Definition Const_sint32_zero     := Const_sint32_zero.
  Definition Const_sint32_one      := Const_sint32_one.
  Definition Const_sint32_2        := Const_sint32_2.
  Definition Const_sint32_3        := Const_sint32_3.
  Definition Const_sint32_4        := Const_sint32_4.
  Definition Const_sint32_5        := Const_sint32_5.
  Definition Const_sint32_6        := Const_sint32_6.
  Definition Const_sint32_7        := Const_sint32_7.
  Definition Const_sint32_8        := Const_sint32_8.
  Definition Const_sint32_9        := Const_sint32_9.
  Definition Const_sint32_10       := Const_sint32_10.
  Definition Const_sint32_mone     := Const_sint32_mone.
  Definition Const_sint32_m2       := Const_sint32_m2.
  Definition Const_sint32_m3       := Const_sint32_m3.
  Definition Const_sint32_m4       := Const_sint32_m4.
  Definition Const_sint32_m5       := Const_sint32_m5.
  Definition Const_sint32_m6       := Const_sint32_m6.
  Definition Const_sint32_m7       := Const_sint32_m7.
  Definition Const_sint32_m8       := Const_sint32_m8.
  Definition Const_sint32_m9       := Const_sint32_m9.
  Definition Const_sint32_m10      := Const_sint32_m10.
  Definition Const_sint32_m11      := Const_sint32_m11.
  Definition Const_sint32_m12      := Const_sint32_m12.
  Definition Const_sint32_neg      := Const_sint32_neg.
  Definition Const_sint32_add      := Const_sint32_add.
  Definition Const_sint32_sub      := Const_sint32_sub.
  Definition Const_sint32_lt       := Const_sint32_lt.
  Definition Const_sint32_le       := Const_sint32_le.
  Definition Const_sint32_to_uint32:= Const_sint32_to_uint32.

  Definition int64CompilableType   := int64CompilableType.
  Definition Const_int64_zero      := Const_int64_zero.
  Definition Const_int64_one       := Const_int64_one.
  Definition Const_int64_2         := Const_int64_2.
  Definition Const_int64_64        := Const_int64_64.

  Definition Const_int64_0xff      := Const_int64_0xff.
  Definition Const_int64_8         := Const_int64_8.
  Definition Const_int64_12        := Const_int64_12.
  Definition Const_int64_32        := Const_int64_32.
  Definition Const_int64_48        := Const_int64_48.
  Definition Const_int64_0x95      := Const_int64_0x95.
  Definition Const_int64_0xfff     := Const_int64_0xfff.
  Definition Const_int64_0xffff    := Const_int64_0xffff.

  (** masking operation*)
  Definition Const_int64_0xf       := Const_int64_0xf.

(*
  Definition Const_int64_max_unsigned := Const_int64_max_unsigned.*)
  Definition Const_int64_neg       := Const_int64_neg.
  Definition Const_int64_add       := Const_int64_add.
  Definition Const_int64_sub       := Const_int64_sub.
  Definition Const_int64_and       := Const_int64_and.
  Definition Const_int64_shr       := Const_int64_shr.
  Definition Const_int64_shru      := Const_int64_shru.
  Definition Const_int64_shl       := Const_int64_shl.
  Definition Const_int64_eq        := Const_int64_eq.
  Definition Const_int64_lt        := Const_int64_lt.
  Definition Const_int64_ltu       := Const_int64_ltu.
  (*
  Definition Const_int64_to_int8   := Const_int64_to_int8.
  Definition Const_sint16_to_int64 := Const_sint16_to_int64.
  Definition Const_int64_to_sint16 := Const_int64_to_sint16.*)
  Definition Const_int64_to_sint32 := Const_int64_to_sint32.
End Exports.
