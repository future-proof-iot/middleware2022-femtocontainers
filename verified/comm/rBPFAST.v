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

Definition well_chunk_Z (chunk: memory_chunk):Z := 
  match chunk with
  | Mint8unsigned => 1
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | _ => 10
  end.

Definition memory_chunk_to_valu32 (chunk: memory_chunk): val := 
  Vint (Int.repr (well_chunk_Z chunk)). (**r well_chunk implies align_chunk, so we didn't need align_chunk, but we must prove a lemma! *)

Definition memory_chunk_to_valu32_upbound (chunk: memory_chunk): val :=
  Vint (Int.repr (Int.max_unsigned-(well_chunk_Z chunk))).

Definition chunk_eqb (c1 c2: memory_chunk) : bool :=
  match c1, c2 with
  | Mint8signed, Mint8signed
  | Mint8unsigned, Mint8unsigned
  | Mint16signed, Mint16signed
  | Mint16unsigned, Mint16unsigned
  | Mint32, Mint32
  | Mint64, Mint64
  | Mfloat32, Mfloat32
  | Mfloat64, Mfloat64
  | Many32, Many32
  | Many64, Many64 => true
  | _, _ => false
  end.

Lemma chunk_eqb_true:
  forall x y, x = y <-> chunk_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma chunk_eqb_false:
  forall x y, x <> y <-> chunk_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.