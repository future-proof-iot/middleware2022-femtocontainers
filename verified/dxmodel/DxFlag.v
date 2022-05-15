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

From Coq Require Import List.
Import ListNotations.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool.

From bpf.comm Require Import Flag.
From bpf.dxcomm Require Import CoqIntegers DxIntegers.

(*
Inductive bpf_flag: Type := 
  | BPF_SUCC_RETURN         (**r =  1, *)
  | BPF_OK                  (**r =  0, *)
  | BPF_ILLEGAL_INSTRUCTION (**r = -1, *)
  | BPF_ILLEGAL_MEM         (**r = -2, *)
  | BPF_ILLEGAL_JUMP        (**r = -3, *)
  | BPF_ILLEGAL_CALL        (**r = -4, *)
  | BPF_ILLEGAL_LEN         (**r = -5, *)
  | BPF_ILLEGAL_REGISTER    (**r = -6  *)
  | BPF_NO_RETURN           (**r = -7, *)
  | BPF_OUT_OF_BRANCHES     (**r = -8, *)
  | BPF_ILLEGAL_DIV         (**r = -9, *)
  | BPF_ILLEGAL_SHIFT       (**r = -10,*)
  | BPF_ILLEGAL_ALU         (**r = -11,*)
  | BPF_UNDEF_ERROR         (**r = -12 *)
.
Lemma bpf_flag_eq: forall (x y: bpf_flag), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

(** flag_eq: flag -> flag -> bool
  *)
Definition flag_eq (x y: bpf_flag): bool := if bpf_flag_eq x y then true else false.
*)
(******************** Dx Related *******************)

(** bpf_flag -> sint32_t *)


Definition flagCompilableType :=
  MkCompilableType bpf_flag C_S32.

Definition flagSymboalType :=
  MkCompilableSymbolType nil (Some flagCompilableType).

Definition Const_BPF_SUCC_RETURN         := constant flagSymboalType BPF_SUCC_RETURN C_S32_one.          (**r =  1, *)
Definition Const_BPF_OK                  := constant flagSymboalType BPF_OK C_S32_zero.                  (**r =  0, *)
Definition Const_BPF_ILLEGAL_INSTRUCTION := constant flagSymboalType BPF_ILLEGAL_INSTRUCTION C_S32_mone. (**r = -1, *)
Definition Const_BPF_ILLEGAL_MEM         := constant flagSymboalType BPF_ILLEGAL_MEM C_S32_m2.           (**r = -2, *)
Definition Const_BPF_ILLEGAL_JUMP        := constant flagSymboalType BPF_ILLEGAL_JUMP C_S32_m3.          (**r = -3, *)
Definition Const_BPF_ILLEGAL_CALL        := constant flagSymboalType BPF_ILLEGAL_CALL C_S32_m4.          (**r = -4, *)
Definition Const_BPF_ILLEGAL_LEN         := constant flagSymboalType BPF_ILLEGAL_LEN C_S32_m5.           (**r = -5, *)
Definition Const_BPF_ILLEGAL_REGISTER    := constant flagSymboalType BPF_ILLEGAL_REGISTER C_S32_m6.      (**r = -6  *)
Definition Const_BPF_NO_RETURN           := constant flagSymboalType BPF_NO_RETURN C_S32_m7.             (**r = -7, *)
Definition Const_BPF_OUT_OF_BRANCHES     := constant flagSymboalType BPF_OUT_OF_BRANCHES C_S32_m8.       (**r = -8, *)
Definition Const_BPF_ILLEGAL_DIV         := constant flagSymboalType BPF_ILLEGAL_DIV C_S32_m9.           (**r = -9, *)
Definition Const_BPF_ILLEGAL_SHIFT       := constant flagSymboalType BPF_ILLEGAL_SHIFT C_S32_m10.        (**r = -10,*)
Definition Const_BPF_ILLEGAL_ALU         := constant flagSymboalType BPF_ILLEGAL_ALU C_S32_m11.          (**r = -11,*)

Definition flagToflagToboolSymbolType :=
  MkCompilableSymbolType [flagCompilableType; flagCompilableType] (Some boolCompilableType).

Definition Const_flag_eq :=
  MkPrimitive flagToflagToboolSymbolType
                flag_eq
                (fun es => match es with
                           | [f1; f2] => Ok (Csyntax.Ebinop Cop.Oeq f1 f2 C_S64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition flagCompilableType            := flagCompilableType.
  Definition Const_BPF_SUCC_RETURN         := Const_BPF_SUCC_RETURN.
  Definition Const_BPF_OK                  := Const_BPF_OK.
  Definition Const_BPF_ILLEGAL_INSTRUCTION := Const_BPF_ILLEGAL_INSTRUCTION.
  Definition Const_BPF_ILLEGAL_MEM         := Const_BPF_ILLEGAL_MEM.
  Definition Const_BPF_ILLEGAL_JUMP        := Const_BPF_ILLEGAL_JUMP.
  Definition Const_BPF_ILLEGAL_CALL        := Const_BPF_ILLEGAL_CALL.
  Definition Const_BPF_ILLEGAL_LEN         := Const_BPF_ILLEGAL_LEN.
  Definition Const_BPF_ILLEGAL_REGISTER    := Const_BPF_ILLEGAL_REGISTER.
  Definition Const_BPF_NO_RETURN           := Const_BPF_NO_RETURN.
  Definition Const_BPF_OUT_OF_BRANCHES     := Const_BPF_OUT_OF_BRANCHES.
  Definition Const_BPF_ILLEGAL_DIV         := Const_BPF_ILLEGAL_DIV.
  Definition Const_BPF_ILLEGAL_SHIFT       := Const_BPF_ILLEGAL_SHIFT.
  Definition Const_BPF_ILLEGAL_ALU         := Const_BPF_ILLEGAL_ALU.
  Definition Const_flag_eq                 := Const_flag_eq.
End Exports.