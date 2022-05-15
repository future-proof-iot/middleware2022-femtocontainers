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

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.
From bpf.comm Require Import BinrBPF.
From bpf.dxcomm Require Import CoqIntegers DxIntegers.
From Coq Require Import List ZArith.
Import ListNotations.

Definition int64TonatSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some natCompilableType).

Definition Const_int64_to_opcode :=
  MkPrimitive int64TonatSymbolType
                get_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end).


Definition Const_int64_to_offset :=
  MkPrimitive int64Tosint32SymbolType
                get_offset
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ecast (Csyntax.Ebinop Cop.Oshr (Csyntax.Ebinop Cop.Oshl e1 C_U64_32 C_U64) C_U64_48 C_U64) C_S16) C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_to_immediate :=
  MkPrimitive int64Tosint32SymbolType
                get_immediate
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oshr e1 C_U64_32 C_U64) C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).


Module Exports.
  Definition Const_int64_to_opcode  := Const_int64_to_opcode.
  Definition Const_int64_to_offset  := Const_int64_to_offset.
  Definition Const_int64_to_immediate := Const_int64_to_immediate.
End Exports.