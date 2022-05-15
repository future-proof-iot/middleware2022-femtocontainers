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
From compcert Require Import Integers Values Memtype Memory.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

From bpf.comm Require Import rBPFMemType.
From bpf.dxcomm Require Import GenMatchable CoqIntegers DxIntegers DxValues.

Open Scope Z_scope.

(** permission_eq_eq: permission_eq -> permission_eq -> bool
  *)
(*
Definition perm_ge (x y: permission): bool := if (Mem.perm_order_dec x y) then true else false.
*)
(******************** Dx Related *******************)

Definition permissionCompilableType :=
  MkCompilableType permission C_U32.

Definition permissionMatchableType :=
  MkMatchableType permissionCompilableType
    (fun x cases =>
      match cases with
      | [f; w; r; n] =>
        Ok (Csyntax.Sswitch x
              (Csyntax.LScons (Some 3) f
                (Csyntax.LScons (Some 2) w
                  (Csyntax.LScons (Some 1) r
                    (Csyntax.LScons (Some 0) n
                      Csyntax.LSnil))))
            )
      | _ => Err MatchEncodingFailed
      end)
    [[]; []; []; []]
    [[]; []; []; []]
    (fun m A r whenR0 whenR1 whenR2 whenR3 =>
      match r with
      | Freeable => whenR0
      | Writable => whenR1
      | Readable => whenR2
      | Nonempty => whenR3
      end).

Definition permissionSymbolType :=
  MkCompilableSymbolType nil (Some permissionCompilableType).

Definition Const_Freeable := constant permissionSymbolType Freeable C_U32_3.

Definition Const_Writable := constant permissionSymbolType Writable C_U32_2.

Definition Const_Readable := constant permissionSymbolType Readable C_U32_one.

Definition Const_Nonempty := constant permissionSymbolType Nonempty C_U32_zero.

Definition permissionTopermissionToboolSymbolType :=
  MkCompilableSymbolType [permissionCompilableType; permissionCompilableType] (Some boolCompilableType).

Definition Const_perm_ge :=
  MkPrimitive permissionTopermissionToboolSymbolType
                perm_ge
                (fun es => match es with
                           | [f1; f2] => Ok (Csyntax.Ebinop Cop.Oge f1 f2 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).


Close Scope Z_scope.

Module Exports.
  Definition permissionMatchableType := permissionMatchableType.
  Definition Const_Freeable          := Const_Freeable.
  Definition Const_Writable          := Const_Writable.
  Definition Const_Readable          := Const_Readable.
  Definition Const_Nonempty          := Const_Nonempty.
  Definition Const_perm_ge           := Const_perm_ge.
End Exports.