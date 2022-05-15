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
From compcert.lib Require Import Integers.


Module MyList.

  Definition t := list int64.
  Definition index_s32 (l: t) (idx: int): int64 := 
    match List.nth_error l (Z.to_nat (Int.unsigned idx)) with
    | Some i => i
    | None => Integers.Int64.zero
    end.
  Definition index_nat (l: t) (idx: nat): int64 := 
    List.nth idx l Integers.Int64.zero.

End MyList.

(** length of MyList should be a extern variable? *)

Definition MyListType := MyList.t.
Definition MyListIndexs32 := MyList.index_s32.
Definition MyListIndexnat := MyList.index_nat.

Definition default_list: MyListType :=  [].