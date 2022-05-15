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
From compcert.common Require Import Values AST Memdata.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

From bpf.comm Require Import rBPFAST.
From bpf.dxcomm Require Import CoqIntegers DxIntegers DxValues.

(******************** Dx Related *******************)

Definition memoryChunkCompilableType :=
  MkCompilableType memory_chunk C_U32.

Definition memoryChunkMatchableType :=
  MkMatchableType memoryChunkCompilableType
    (fun x cases =>
      match cases with
      | [s8; u8; s16; u16; s32; s64; f32; f64; a32; a64] =>
        Ok (Csyntax.Sswitch x
              (Csyntax.LScons (Some 1%Z) u8
                (Csyntax.LScons (Some 2%Z) u16
                  (Csyntax.LScons (Some 4%Z) s32
                    (Csyntax.LScons (Some 8%Z) s64
                      (Csyntax.LScons None s8
                      Csyntax.LSnil)))))
            )
      | _ => Err MatchEncodingFailed
      end)
    [[]; []; []; []; []; []; []; []; []; []]
    [[]; []; []; []; []; []; []; []; []; []]
    (fun m A r whenR0 whenR1 whenR2 whenR3 whenR4 whenR5 whenR6 whenR7 whenR8 whenR9 =>
      match r with
      | Mint8signed => whenR0
      | Mint8unsigned => whenR1
      | Mint16signed => whenR2
      | Mint16unsigned => whenR3
      | Mint32 => whenR4
      | Mint64 => whenR5
      | Mfloat32 => whenR6
      | Mfloat64 => whenR7
      | Many32 => whenR8
      | Many64 => whenR9
      end).

Open Scope Z_scope.

Definition memoryChunkSymbolType :=
  MkCompilableSymbolType nil (Some memoryChunkCompilableType).

Definition Const_Mint8unsigned := constant memoryChunkSymbolType Mint8unsigned C_U32_one.

Definition Const_Mint16unsigned := constant memoryChunkSymbolType Mint16unsigned C_U32_2.

Definition Const_Mint32 := constant memoryChunkSymbolType Mint32 C_U32_4.

Definition Const_Mint64 := constant memoryChunkSymbolType Mint64 C_U32_8.

Definition memoryChunkToboolSymbolType :=
  MkCompilableSymbolType [memoryChunkCompilableType] (Some boolCompilableType).

Definition memoryChunkTovalU32SymbolType :=
  MkCompilableSymbolType [memoryChunkCompilableType] (Some valU32CompilableType).

Definition Const_memory_chunk_to_valu32 :=
  MkPrimitive memoryChunkTovalU32SymbolType
                memory_chunk_to_valu32
                (fun es => match es with
                           | [e1] => Ok e1 (**r e1 -> (Csyntax.Ecast  e1 C_U64), dx doesn't know this issue *)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_memory_chunk_to_valu32_upbound :=
  MkPrimitive memoryChunkTovalU32SymbolType
                memory_chunk_to_valu32_upbound
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ebinop Cop.Osub C_U32_max_unsigned e1 C_U32) (**r e1 -> (Csyntax.Ecast  e1 C_U64), dx doesn't know this issue *)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition memoryChunkMatchableType  := memoryChunkMatchableType.
  Definition Const_Mint8unsigned       := Const_Mint8unsigned.
  Definition Const_Mint16unsigned      := Const_Mint16unsigned.
  Definition Const_Mint32              := Const_Mint32.
  Definition Const_Mint64              := Const_Mint64.
  Definition Const_memory_chunk_to_valu32:= Const_memory_chunk_to_valu32.
  Definition Const_memory_chunk_to_valu32_upbound := Const_memory_chunk_to_valu32_upbound.
End Exports.