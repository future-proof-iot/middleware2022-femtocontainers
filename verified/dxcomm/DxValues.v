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
From dx.Type Require Import Bool Nat.

From bpf.comm Require Import rBPFValues.
From bpf.dxcomm Require Import InfComp CoqIntegers DxIntegers.

(** Coq2C: Values.val -> unsigned long long or unsigned int
  *)

(******************** Val2PTR *******************)
Definition valptr8_t := val.
Definition valptr_null := Vnullptr.

Definition C_U8ptr_zero: Csyntax.expr :=
  Csyntax.Eval valptr_null C_U8_pointer.

(*
Definition comp_eq_ptr8_zero (x: val): bool :=
  match x with
  | Vint n1 => Int.eq n1 Int.zero
  | _ => false
  end. *)

Definition valptr8CompilableType :=
  MkCompilableType valptr8_t C_U8_pointer.

Definition valptr8SymbolType :=
  MkCompilableSymbolType nil (Some valptr8CompilableType).

Definition Const_valptr_null := constant valptr8SymbolType valptr_null C_U8ptr_zero.
(*
Definition valptr8ToboolSymbolType :=
  MkCompilableSymbolType [valptr8CompilableType] (Some boolCompilableType).

Definition C_U8ptr_eq (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oeq x y C_U8_pointer.

Definition Const_comp_eq_ptr8_zero :=
  MkPrimitive valptr8ToboolSymbolType
                comp_eq_ptr8_zero
                (fun es => match es with
                           | [e1] => Ok (C_U8ptr_eq e1 C_U8ptr_zero)
                           | _       => Err PrimitiveEncodingFailed
                           end). *)

(******************** Val2U32 *******************)

Definition valu32_t := val.

Definition val32_zero := Vint int32_0. (**r ==> Nonempty *)
Definition val32_one  := Vint int32_1.   (**r ==> Readable *)
Definition val32_2    := Vint int32_2. (**r ==> Writable *)
Definition val32_3    := Vint int32_3. (**r ==> Freeable *)
Definition val32_32   := Vint int32_32.
Definition val32_64   := Vint int32_64.
Definition val32_max_unsigned := Vint int32_max_unsigned.
(*
(** Type signature: val -> val -> option val
    we use `val32_divu` to replace `Val.divu`
  *)

Definition val32_divu (x y: val): val :=
  match Val.divu x y with
  | Some res => res
  | None => Vundef
  end.

(** Type signature: val -> val -> option val
    we use `val32_modu` to replace `Val.modu`
  *)

Definition val32_modu (x y: val): val :=
  match Val.modu x y with
  | Some res => res
  | None => Vundef
  end.

Definition comp_eq_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => Int.eq n1 n2
  | _, _ => false
  end.

Definition comp_ne_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => negb (Int.eq n1 n2)
  | _, _ => false
  end.

Definition compu_lt_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => Int.ltu n1 n2
  | _, _ => false
  end.

Definition compu_le_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => negb (Int.ltu n2 n1)
  | _, _ => false
  end.
*)
(******************** Val2S32 *******************)

Definition vals32_t := val.

(******************** Val2U64 *******************)

Definition val64_t := val.

Definition val64_zero := Vlong Int64.zero.
Definition val64_64 := Vlong int64_64.

(******************** Val2S64 *******************)

Definition vals64_t := val.

Definition vals64_zero := Vlong Int64.zero.
Definition vals64_64 := Vlong int64_64.

 (*
Definition val64_max_unsigned := Vlong int64_max_unsigned.*)
(*
(** Type signature: val -> val -> option val
    we use `val64_divlu` to replace `Val.divlu`
  *)

Definition val64_divlu (x y: val): val :=
  match Val.divlu x y with
  | Some res => res
  | None => Vundef
  end.

(** Type signature: val -> val -> option val
    we use `val32_modlu` to replace `Val.modlu`
  *)

Definition val64_modlu (x y: val): val :=
  match Val.modlu x y with
  | Some res => res
  | None => Vundef
  end.
(** To avoid defining the matchableType of comparison in dx, we define unique comparison functions *)

Definition compl_eq (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.eq n1 n2
  | _, _ => false
  end.
Definition compl_ne (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.eq n1 n2)
  | _, _ => false
  end.
Definition compl_lt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.lt n1 n2
  | _, _ => false
  end.
Definition compl_le (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.lt n2 n1)
  | _, _ => false
  end.
Definition compl_gt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.lt n2 n1
  | _, _ => false
  end.
Definition compl_ge (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.lt n1 n2)
  | _, _ => false
  end.
Definition complu_lt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.ltu n1 n2
  | _, _ => false
  end.
Definition complu_le (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.ltu n2 n1)
  | _, _ => false
  end.
Definition complu_gt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.ltu n2 n1
  | _, _ => false
  end.
Definition complu_ge (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.ltu n1 n2)
  | _, _ => false
  end.
Definition complu_set (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.eq (Int64.and n1 n2) Int64.zero)
  | _, _ => false
  end.

(******************** Val Type Casting *******************)

(** ptr2valu32: ptr -> u32

*)
(*
Definition ptr2valu32 (ptr: valptr32_t): valu32_t :=
  match ptr with
  | Vptr _ _ => here we need memory_region information...*)

(** sint16_to_vlong: sint16_t -> Val
    *)
Definition sint16_to_vlong (i:sint16_t): val :=
  Vlong (Int64.repr (Int16.signed i)).

(** _to_u32 : vlong_to_vint <==> val_intoflongu
  *)

Definition val_intuoflongu (v: val): val :=
  match v with
  | Vlong n    => Vint (Int.repr (Int64.unsigned n))
  | _          => Vundef
  end.

(** _to_S32 : vlong_to_vint <==> val_intsoflongu
  *)

Definition val_intsoflongu (v: val): val :=
  match v with
  | Vlong n    => Vint (Int.repr (Int64.unsigned n))
  | _          => Vundef
  end.
(** sint32_to_vlong: sint32 -> Vlong
  *)
Definition sint32_to_vint (v: sint32_t): val := Vint v.
(** int64_to_vlong: long -> Vlong
  *)
Definition int64_to_vlong (v: int64): val := Vlong v.
*)
(******************** Dx Related *******************)


(******************** Val2U32 *******************)

Definition valU32CompilableType :=
  MkCompilableType valu32_t C_U32.

Definition valU32SymbolType :=
  MkCompilableSymbolType nil (Some valU32CompilableType).

Definition Const_val32_zero := constant valU32SymbolType val32_zero C_U32_zero.
Definition Const_val32_one  := constant valU32SymbolType val32_one  C_U32_one.
Definition Const_val32_2    := constant valU32SymbolType val32_2    C_U32_2.
Definition Const_val32_3    := constant valU32SymbolType val32_3    C_U32_3.

Definition Const_val32_32 := constant valU32SymbolType val32_32 C_U32_32.
Definition Const_val32_64 := constant valU32SymbolType val32_64 C_U32_64.

Definition Const_val32_max_unsigned := constant valU32SymbolType val32_max_unsigned C_U32_max_unsigned.

(** Type signature: val -> val
  *)
Definition valU32TovalU32SymbolType :=
  MkCompilableSymbolType [valU32CompilableType] (Some valU32CompilableType).

Definition Const_valU32_neg :=
  MkPrimitive valU32TovalU32SymbolType
                Val.neg
                (fun es => match es with
                           | [e1] => Ok (C_U32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: val -> val -> val
  *)
Definition valU32TovalU32TovalU32SymbolType :=
  MkCompilableSymbolType [valU32CompilableType; valU32CompilableType] (Some valU32CompilableType).

Instance C_valu32 : CType valu32_t := mkCType _ (cType valU32CompilableType).

Definition Const_valU32_add := ltac: (mkprimitive Val.add (binop_expr Cop.Oadd C_U32)).
Definition Const_valU32_sub := ltac: (mkprimitive Val.sub (binop_expr Cop.Osub C_U32)).
Definition Const_valU32_mul := ltac: (mkprimitive Val.mul (binop_expr Cop.Omul C_U32)).
Definition Const_valU32_div := ltac: (mkprimitive val32_divu (binop_expr Cop.Odiv C_U32)).
Definition Const_valU32_or  := ltac: (mkprimitive Val.or  (binop_expr Cop.Oor  C_U32)).
Definition Const_valU32_and := ltac: (mkprimitive Val.and (binop_expr Cop.Oand C_U32)).
Definition Const_valU32_shl := ltac: (mkprimitive Val.shl (binop_expr Cop.Oshl C_U32)).
Definition Const_valU32_shr := ltac: (mkprimitive Val.shru (binop_expr Cop.Oshr C_U32)).
Definition Const_valU32_mod := ltac: (mkprimitive val32_modu (binop_expr Cop.Omod C_U32)).
Definition Const_valU32_xor := ltac: (mkprimitive Val.xor (binop_expr Cop.Oxor C_U32)).

Definition Const_valU32_shrs :=
  MkPrimitive valU32TovalU32TovalU32SymbolType
                Val.shr
                (fun es => match es with
                           | [e1; e2] => Ok (C_U32_shr (Csyntax.Ecast  e1 C_S32) e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition valU32TovalU32ToboolSymbolType :=
  MkCompilableSymbolType [valU32CompilableType; valU32CompilableType] (Some boolCompilableType).

Instance C_bool : CType bool := mkCType _ (cType boolCompilableType).

Definition Const_valU32_eq  := ltac: (mkprimitive comp_eq_32 (binop_expr Cop.Oeq C_U32)).
Definition Const_valU32_ne  := ltac: (mkprimitive comp_ne_32 (binop_expr Cop.One C_U32)).
Definition Const_valU32_ltu := ltac: (mkprimitive compu_lt_32 (binop_expr Cop.Olt C_U32)).

Definition Const_valU32_le := ltac: (mkprimitive compu_le_32 (binop_expr Cop.Ole C_U32)).

(******************** Val2S32 *******************)

Definition valS32CompilableType :=
  MkCompilableType vals32_t C_S32.

(** Type signature: val -> val
  *)
Definition valS32TovalS32SymbolType :=
  MkCompilableSymbolType [valS32CompilableType] (Some valS32CompilableType).

Definition Const_valS32_neg :=
  MkPrimitive valS32TovalS32SymbolType
                Val.neg
                (fun es => match es with
                           | [e1] => Ok (C_S32_neg e1) (** Csyntax.Eunop Cop.Oneg x C_S32. *)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: val -> val -> val
  *)
Definition valS32TovalS32TovalS32SymbolType :=
  MkCompilableSymbolType [valS32CompilableType; valS32CompilableType] (Some valS32CompilableType).

Definition Const_valS32_add :=
  MkPrimitive valS32TovalS32TovalS32SymbolType
                Val.add
                (fun es => match es with
                           | [e1; e2] => Ok (C_S32_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Val2U64 *******************)
Definition val64CompilableType :=
  MkCompilableType val64_t C_U64.

Definition val64SymbolType :=
  MkCompilableSymbolType nil (Some val64CompilableType).

Definition Const_val64_zero := constant val64SymbolType val64_zero C_U64_zero.

Definition Const_val64_64 := constant val64SymbolType val64_64 C_U64_64.
(*
Definition Const_val64_max_unsigned := constant val64SymbolType val64_max_unsigned C_U64_max_unsigned.*)

(** Type signature: val -> val
  *)
Definition val64Toval64SymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some val64CompilableType).

Definition Const_val64_neg :=
  MkPrimitive val64Toval64SymbolType
                Val.negl
                (fun es => match es with
                           | [e1] => Ok (C_U64_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).


Instance C_val64 : CType val64_t := mkCType _ (cType val64CompilableType).

Definition Const_val64_add := ltac: (mkprimitive Val.addl (binop_expr Cop.Oadd C_U64)).
Definition Const_val64_sub := ltac: (mkprimitive Val.subl (binop_expr Cop.Osub C_U64)).
Definition Const_val64_mul := ltac: (mkprimitive Val.mull (binop_expr Cop.Omul C_U64)).
Definition Const_val64_div := ltac: (mkprimitive val64_divlu (binop_expr Cop.Odiv C_U64)).
Definition Const_val64_or  := ltac: (mkprimitive Val.orl  (binop_expr Cop.Oor  C_U64)).
Definition Const_val64_and := ltac: (mkprimitive Val.andl (binop_expr Cop.Oand C_U64)).
Definition Const_val64_shl := ltac: (mkprimitive Val.shll (binop_expr Cop.Oshl C_U64)).
Definition Const_val64_shr := ltac: (mkprimitive Val.shrlu (binop_expr Cop.Oshr C_U64)).
Definition Const_val64_mod := ltac: (mkprimitive val64_modlu (binop_expr Cop.Omod C_U64)).
Definition Const_val64_xor := ltac: (mkprimitive Val.xorl (binop_expr Cop.Oxor C_U64)).

(******************** Val2S64 *******************)
Definition valS64CompilableType :=
  MkCompilableType vals64_t C_S64.


(** S32_to_S64: Val_slongofint
  *)

Definition Val_slongofint (i:int) := Val.longofint (Vint i).
Definition valS32TovalS64SymbolType :=
  MkCompilableSymbolType [sint32CompilableType] (Some valS64CompilableType).

Definition Const_valS32TovalS64 :=
  MkPrimitive valS32TovalS64SymbolType
                Val_slongofint
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_S64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** S64_to_U64: Val_ulongofslong
  *)
Definition Val_ulongofslong (i:val) := i.
Definition valS64TovalU64SymbolType :=
  MkCompilableSymbolType [valS64CompilableType] (Some val64CompilableType).

Definition Const_valS64TovalU64 :=
  MkPrimitive valS64TovalU64SymbolType
                Val_ulongofslong
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: val -> val -> val
  *)
Definition val64Toval64Toval64SymbolType :=
  MkCompilableSymbolType [val64CompilableType; val64CompilableType] (Some val64CompilableType).

Definition Const_val64_shrs := ltac: (mkprimitive Val.shrl (binop_expr_cast1 Cop.Oshr C_S64 C_U64)).

Definition val64Toval64ToboolSymbolType :=
  MkCompilableSymbolType [val64CompilableType; val64CompilableType] (Some boolCompilableType).

Definition Const_val64_eq := ltac: (mkprimitive compl_eq (binop_expr Cop.Oeq C_U64)).
Definition Const_val64_ne := ltac: (mkprimitive compl_ne (binop_expr Cop.One C_U64)).

Definition Const_val64u_lt := ltac: (mkprimitive complu_lt (binop_expr Cop.Olt C_U64)).
Definition Const_val64u_le := ltac: (mkprimitive complu_le (binop_expr Cop.Ole C_U64)).
Definition Const_val64u_gt := ltac: (mkprimitive complu_gt (binop_expr Cop.Ogt C_U64)).
Definition Const_val64u_ge := ltac: (mkprimitive complu_ge (binop_expr Cop.Oge C_U64)).

Definition Const_val64s_lt := ltac: (mkprimitive compl_lt (binop_expr_cast2 Cop.Olt C_S64 C_U64)).
Definition Const_val64s_le := ltac: (mkprimitive compl_le (binop_expr_cast2 Cop.Ole C_S64 C_U64)).
Definition Const_val64s_gt := ltac: (mkprimitive compl_gt (binop_expr_cast2 Cop.Ogt C_S64 C_U64)).
Definition Const_val64s_ge := ltac: (mkprimitive compl_ge (binop_expr_cast2 Cop.Oge C_S64 C_U64)).


Definition Const_complu_set :=
  MkPrimitive val64Toval64ToboolSymbolType
                complu_set
                (fun es => match es with
                           | [e1; e2] => Ok (Csyntax.Ebinop Cop.One
                                              (Csyntax.Ebinop Cop.Oand e1 e2 C_U64)
                                               C_U64_zero  C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Val Type Casting *******************)
(*
Definition sint16Toval64SymbolType :=
  MkCompilableSymbolType [sint16CompilableType] (Some val64CompilableType).

Definition Const_sint16_to_vlong :=
  MkPrimitive sint16Toval64SymbolType
                sint16_to_vlong
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).*)

Definition val64TovalU32SymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some valU32CompilableType).

Definition Const_val64TovalU32 :=
  MkPrimitive val64TovalU32SymbolType
                val_intuoflongu
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition val64TovalS32SymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some valS32CompilableType).

Definition Const_val64TovalS32 :=
  MkPrimitive val64TovalS32SymbolType
                val_intsoflongu
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition sint32Tosval32SymbolType :=
  MkCompilableSymbolType [sint32CompilableType] (Some valS32CompilableType).

Definition Const_sint32_to_vint :=
  MkPrimitive sint32Tosval32SymbolType
                sint32_to_vint
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition svint_to_uvint (v:val) := v.

Definition svint32Touval32SymbolType :=
  MkCompilableSymbolType [valS32CompilableType] (Some valU32CompilableType).

Definition Const_svint_to_uvint :=
  MkPrimitive svint32Touval32SymbolType
                svint_to_uvint
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).


Definition int64Toval64SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some val64CompilableType).

Definition Const_int64_to_vlong :=
  MkPrimitive int64Toval64SymbolType
                int64_to_vlong
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** S32_to_U64: Val.longofint
  *)
Definition valS32Toval64SymbolType :=
  MkCompilableSymbolType [valS32CompilableType] (Some val64CompilableType).

Definition Const_valS32Toval64 :=
  MkPrimitive valS32Toval64SymbolType
                Val.longofint
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** U32_to_U64: Val.longofintu
  *)
Definition valU32Toval64SymbolType :=
  MkCompilableSymbolType [valU32CompilableType] (Some val64CompilableType).

Definition Const_valU32Toval64 :=
  MkPrimitive valU32Toval64SymbolType
                Val.longofintu
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition valptr8CompilableType := valptr8CompilableType.
  Definition Const_valptr_null      := Const_valptr_null. (*
  Definition Const_comp_eq_ptr8_zero:= Const_comp_eq_ptr8_zero. *)

  Definition valU32CompilableType   := valU32CompilableType.
  Definition Const_val32_zero       := Const_val32_zero.
  Definition Const_val32_one        := Const_val32_one.
  Definition Const_val32_2          := Const_val32_2.
  Definition Const_val32_3          := Const_val32_3.
  Definition Const_val32_32         := Const_val32_32.
  Definition Const_val32_64         := Const_val32_64.
  Definition Const_val32_max_unsigned := Const_val32_max_unsigned.
  Definition Const_valU32_neg       := Const_valU32_neg.
  Definition Const_valU32_add       := Const_valU32_add.
  Definition Const_valU32_sub       := Const_valU32_sub.
  Definition Const_valU32_mul       := Const_valU32_mul.
  Definition Const_valU32_div       := Const_valU32_div.
  Definition Const_valU32_or        := Const_valU32_or.
  Definition Const_valU32_and       := Const_valU32_and.
  Definition Const_valU32_shl       := Const_valU32_shl.
  Definition Const_valU32_shr       := Const_valU32_shr.
  Definition Const_valU32_mod       := Const_valU32_mod.
  Definition Const_valU32_xor       := Const_valU32_xor.
  Definition Const_valU32_shrs      := Const_valU32_shrs.
  Definition Const_valU32_eq        := Const_valU32_eq.
  Definition Const_valU32_ne        := Const_valU32_ne.
  Definition Const_valU32_ltu       := Const_valU32_ltu.
  Definition Const_valU32_le        := Const_valU32_le.

  Definition valS32CompilableType   := valS32CompilableType.
  Definition Const_valS32_neg       := Const_valS32_neg.
  Definition Const_valS32_add       := Const_valS32_add.

  Definition val64CompilableType    := val64CompilableType.
  Definition Const_val64_zero       := Const_val64_zero.
  Definition Const_val64_64         := Const_val64_64. (*
  Definition Const_val64_max_unsigned := Const_val64_max_unsigned.*)
  Definition Const_val64_neg        := Const_val64_neg.
  Definition Const_val64_add        := Const_val64_add.
  Definition Const_val64_sub        := Const_val64_sub.
  Definition Const_val64_mul        := Const_val64_mul.
  Definition Const_val64_div        := Const_val64_div.
  Definition Const_val64_or         := Const_val64_or.
  Definition Const_val64_and        := Const_val64_and.
  Definition Const_val64_shl        := Const_val64_shl.
  Definition Const_val64_shr        := Const_val64_shr.
  Definition Const_val64_mod        := Const_val64_mod.
  Definition Const_val64_xor        := Const_val64_xor.
  Definition Const_val64_shrs       := Const_val64_shrs.

  Definition Const_val64_eq         := Const_val64_eq.
  Definition Const_val64_ne         := Const_val64_ne.
  Definition Const_val64s_lt        := Const_val64s_lt.
  Definition Const_val64s_le        := Const_val64s_le.
  Definition Const_val64s_gt        := Const_val64s_gt.
  Definition Const_val64s_ge        := Const_val64s_ge.
  Definition Const_val64u_lt        := Const_val64u_lt.
  Definition Const_val64u_le        := Const_val64u_le.
  Definition Const_val64u_gt        := Const_val64u_gt.
  Definition Const_val64u_ge        := Const_val64u_ge.
  Definition Const_complu_set       := Const_complu_set.

  Definition valS64CompilableType   := valS64CompilableType.
  Definition Const_valS32TovalS64   := Const_valS32TovalS64.
  Definition Const_valS64TovalU64   := Const_valS64TovalU64.
(*
  Definition Const_sint16_to_vlong  := Const_sint16_to_vlong.*)
  Definition Const_val64TovalU32    := Const_val64TovalU32.
  Definition Const_val64TovalS32    := Const_val64TovalS32.
  Definition Const_sint32_to_vint   := Const_sint32_to_vint.
  Definition Const_svint_to_uvint   := Const_svint_to_uvint.
  Definition Const_int64_to_vlong   := Const_int64_to_vlong.
  Definition Const_valS32Toval64    := Const_valS32Toval64.
  Definition Const_valU32Toval64    := Const_valU32Toval64.
End Exports.
