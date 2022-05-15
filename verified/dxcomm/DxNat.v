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

Require Import List.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert Require Import Integers Values.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool.

From bpf.dxcomm Require Import CoqIntegers DxIntegers.
From Coq Require Import ZArith Number Decimal.

(* Derive Nat as unsigned int *)
(* To ensure soundness, S is not derived as +1, only O is derivable *)
(* One can still provide a primitive encoding for specific constants *)
Open Scope nat_scope.

Definition nat8 := nat.
Definition nat8_1 := 1.
Definition nat32_1 := 1.

Definition nat8_536870911 := Init.Nat.of_num_uint (UIntDecimal (D5 (D3 (D6 (D8 (D7 (D0 (D9 (D1 (D1 Nil)))))))))).

(** masking operation *)
Definition nat8_0xf0 := 0xf0.
Definition nat8_0x07 := 0x07.
Definition nat8_0xff := 0xff.
Definition nat8_0x08 := 0x08.
Definition nat8_zero := 0x00.

Definition nat8_0x05 := 0x05.
Definition nat8_0x84 := 0x84.
Definition nat8_0x87 := 0x87.
Definition nat8_0x85 := 0x85.
Definition nat8_0x95 := 0x95.

Definition nat8CompilableType :=
  MkCompilableType nat8 C_U8.

Definition C_NAT8_1: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_1))) C_U8.

Definition C_NAT32_1: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat32_1))) C_U32.

(**r masking operations *)
Definition C_NAT8_0xf0: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0xf0))) C_U8.

Definition C_NAT8_0x07: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x07))) C_U8.

Definition C_NAT8_0xff: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0xff))) C_U8.

Definition C_NAT8_0x08: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x08))) C_U8.

Definition C_NAT8_0x00: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_zero))) C_U8.

Definition C_NAT8_0x05: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x05))) C_U8.

Definition C_NAT8_0x84: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x84))) C_U8.

Definition C_NAT8_0x87: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x87))) C_U8.

Definition C_NAT8_0x85: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x85))) C_U8.

Definition C_NAT8_0x95: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x95))) C_U8.

Definition C_NAT8_536870911: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_536870911))) C_U8.



Definition nat8SymbolType :=
  MkCompilableSymbolType nil (Some nat8CompilableType).

Definition Const_nat8_1    := constant nat8SymbolType nat8_1    C_NAT8_1.
Definition Const_nat32_1   := constant nat8SymbolType nat32_1   C_NAT32_1.
Definition Const_nat8_0xf0 := constant nat8SymbolType nat8_0xf0 C_NAT8_0xf0.
Definition Const_nat8_0x07 := constant nat8SymbolType nat8_0x07 C_NAT8_0x07.
Definition Const_nat8_0xff := constant nat8SymbolType nat8_0xff C_NAT8_0xff.
Definition Const_nat8_0x08 := constant nat8SymbolType nat8_0x08 C_NAT8_0x08.
Definition Const_nat8_zero := constant nat8SymbolType nat8_zero C_NAT8_0x00.
Definition Const_nat8_0x05 := constant nat8SymbolType nat8_0x05 C_NAT8_0x05.
Definition Const_nat8_0x84 := constant nat8SymbolType nat8_0x84 C_NAT8_0x84.
Definition Const_nat8_0x87 := constant nat8SymbolType nat8_0x87 C_NAT8_0x87.
Definition Const_nat8_0x85 := constant nat8SymbolType nat8_0x85 C_NAT8_0x85.
Definition Const_nat8_0x95 := constant nat8SymbolType nat8_0x95 C_NAT8_0x95.
Definition Const_nat8_536870911 := constant nat8SymbolType nat8_536870911 C_NAT8_536870911.

Definition nat8Tonat8ToboolSymbolType :=
  MkCompilableSymbolType [nat8CompilableType; nat8CompilableType] (Some boolCompilableType).

Definition C_NAT8_eq (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oeq x y C_U8.

Definition Const_nat8_eq :=
  MkPrimitive nat8Tonat8ToboolSymbolType
                Nat.eqb
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_eq e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition C_NAT8_le (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Ole x y C_U8.

Definition Const_nat8_le :=
  MkPrimitive nat8Tonat8ToboolSymbolType
                Nat.leb
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_le e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).



Definition nat8Tonat8Tonat8SymbolType :=
  MkCompilableSymbolType [nat8CompilableType; nat8CompilableType] (Some nat8CompilableType).

Definition C_NAT8_and (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oand x y C_U8.

Definition Const_nat8_and :=
  MkPrimitive nat8Tonat8Tonat8SymbolType
                Nat.land
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_and e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition C_NAT8_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U8.

Definition Const_nat8_sub :=
  MkPrimitive nat8Tonat8Tonat8SymbolType
                Nat.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition nat2int (n:nat) := (Int.repr (Z.of_nat n)).

Definition nat8Touint32SymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some uint32CompilableType).

Definition Const_nat2int :=
  MkPrimitive nat8Touint32SymbolType
                nat2int
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition nat8CompilableType := nat8CompilableType.
  Definition Const_nat8_1       := Const_nat8_1.
  Definition Const_nat32_1      := Const_nat32_1.
  Definition Const_nat8_0xf0    := Const_nat8_0xf0.
  Definition Const_nat8_0x07    := Const_nat8_0x07.
  Definition Const_nat8_0xff    := Const_nat8_0xff.
  Definition Const_nat8_0x08    := Const_nat8_0x08.
  Definition Const_nat8_0x05    := Const_nat8_0x05.
  Definition Const_nat8_0x84    := Const_nat8_0x84.
  Definition Const_nat8_0x87    := Const_nat8_0x87.
  Definition Const_nat8_0x85    := Const_nat8_0x85.
  Definition Const_nat8_0x95    := Const_nat8_0x95.
  Definition Const_nat8_zero    := Const_nat8_zero.
  Definition Const_nat8_eq      := Const_nat8_eq.
  Definition Const_nat8_le      := Const_nat8_le.
  Definition Const_nat8_and     := Const_nat8_and.
  Definition Const_nat8_sub     := Const_nat8_sub.
  Definition Const_nat2int      := Const_nat2int.
  Definition Const_nat8_536870911 := Const_nat8_536870911.
End Exports.
