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

From bpf.comm Require Import rBPFMemType.

Record memory_region : Type := mkmr{
  start_addr : val;
  block_size : val;   (**r should those be val32_t? *)
  block_perm : permission; (**r let's say it should be u32 *)
  block_ptr  : val;
}.

Definition default_memory_region := {|
  start_addr := Vnullptr;
  block_size := Vzero;
  block_perm := Nonempty;
  block_ptr  := Vnullptr;
|}.

Module Memory_regions.

  Definition t := list memory_region.
  Definition index_nat (l: t) (idx: nat): memory_region :=
    match List.nth_error l idx with
    | Some mr => mr
    | None => default_memory_region
    end.

End Memory_regions.

Definition MyMemRegionsType := Memory_regions.t.
Definition MyMemRegionsIndexnat := Memory_regions.index_nat.

Definition default_memory_regions: MyMemRegionsType :=  [].

Fixpoint MyMemRegionsAdd (mr: memory_region) (l: MyMemRegionsType) :=
  match l with
  | [] => [mr]
  | hd :: tl => hd :: MyMemRegionsAdd mr tl
  end.