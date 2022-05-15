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
From compcert Require Import Integers Values Memtype.

From dx Require Import ResultMonad IR IRtoC.
From dx.Type Require Import Nat.

From bpf.comm Require Import MemRegion.
From bpf.dxcomm Require Import CoqIntegers DxIntegers DxValues.
From bpf.dxmodel Require Import IdentDef DxMemType.

Fixpoint MyMemRegionsAdd (mr: memory_region) (l: MyMemRegionsType) :=
  match l with
  | [] => [mr]
  | hd :: tl => hd :: MyMemRegionsAdd mr tl
  end.


(******************** Dx Related *******************)

Definition mem_region_type: Ctypes.type := Ctypes.Tpointer (Ctypes.Tstruct mem_region_id Ctypes.noattr) Ctypes.noattr.

Definition mem_region_def: Ctypes.composite_definition := 
  Ctypes.Composite mem_region_id Ctypes.Struct [(start_addr_id, C_U32); (size_id, C_U32); (perm_id, C_U32); (block_ptr_id, C_U8_pointer)] Ctypes.noattr.

Definition mem_regionCompilableType := MkCompilableType memory_region mem_region_type.

(** Type for mem_region -> valptr8_t *)

Definition mem_regionToValU8PTRCompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some valptr8CompilableType).

Definition Const_block_ptr := 
  MkPrimitive mem_regionToValU8PTRCompilableSymbolType 
              block_ptr
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) block_ptr_id C_U8_pointer)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** Type for mem_region -> valu32_t *)

Definition mem_regionToValU32CompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some valU32CompilableType).

Definition mem_regionTopermCompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some permissionCompilableType).


Definition Const_start_addr := 
  MkPrimitive mem_regionToValU32CompilableSymbolType 
              start_addr
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) start_addr_id C_U32)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_block_size := 
  MkPrimitive mem_regionToValU32CompilableSymbolType 
              block_size
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) size_id C_U32)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Definition Const_block_perm := 
  MkPrimitive mem_regionTopermCompilableSymbolType 
              block_perm
              (fun es => match es with
                         | [e1] => Ok (Csyntax.Efield (Csyntax.Ederef e1 mem_region_type) perm_id C_U32)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** "Mapping relations from Coq to C":
  Coq:                  -> C:
  l:list memory_region  -> mem_region_type *l
  get l idx             -> *(l+idx)
 *)

Definition get_index (x idx: Csyntax.expr): Csyntax.expr :=
  (*Csyntax.Eindex x idx mem_region_type.*)
  Csyntax.Ebinop Cop.Oadd x idx (Ctypes.Tpointer mem_region_type Ctypes.noattr).

(** Coq2C: l:list memory_region  -> memory_region *l *)
Definition MyMemRegionsCompilableType :=
  MkCompilableType MyMemRegionsType mem_region_type.

(** Type for MyMemRegions.t -> nat -> memory_region *)
Definition MyMemRegionsToNatToMemRegionCompilableSymbolType :=
  MkCompilableSymbolType [MyMemRegionsCompilableType; natCompilableType] (Some mem_regionCompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndexNatPrimitive := 
  MkPrimitive MyMemRegionsToNatToMemRegionCompilableSymbolType 
              MyMemRegionsIndexnat
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition mem_regionCompilableType   := mem_regionCompilableType.
  Definition Const_block_ptr            := Const_block_ptr.
  Definition Const_start_addr           := Const_start_addr.
  Definition Const_block_size           := Const_block_size.
  Definition Const_block_perm           := Const_block_perm.
  Definition MyMemRegionsCompilableType := MyMemRegionsCompilableType.
  Definition myListIndexNatPrimitive    := myListIndexNatPrimitive.
End Exports.
