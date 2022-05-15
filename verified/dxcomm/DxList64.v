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
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

From bpf.comm Require Import List64.
From bpf.dxcomm Require Import CoqIntegers DxIntegers.

(******************** Dx Related *******************)

(** "Mapping relations from Coq to C":
  Coq:          -> C:
  l:list state  -> uint64_t *l
  get l idx     -> *(l+idx)
 *)

Definition get_index (x idx: Csyntax.expr): Csyntax.expr :=
  Csyntax.Eindex x idx C_U64.

(** Coq2C: l:list u64_t  -> uint64_t *l *)
Definition MyListCompilableType :=
  MkCompilableType MyListType C_U64_pointer.

(** Type for MyList.t -> u64_t -> u64_t *)
Definition MyListToStateToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyListCompilableType; sint32CompilableType] (Some int64CompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndexs32Primitive := 
  MkPrimitive MyListToStateToStateCompilableSymbolType 
              MyListIndexs32
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** Type for MyList.t -> nat -> u64_t *)
Definition MyListToNatToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyListCompilableType; natCompilableType] (Some int64CompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndexnatPrimitive := 
  MkPrimitive MyListToNatToStateCompilableSymbolType 
              MyListIndexnat
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition MyListCompilableType    := MyListCompilableType.
  Definition myListIndexs32Primitive := myListIndexs32Primitive.
  Definition myListIndexnatPrimitive := myListIndexnatPrimitive.
End Exports.
