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

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.

From bpf.comm Require Import List64 BinrBPF.

From Coq Require Import List ZArith.
Import ListNotations.

Record state := mkst {
  ins_len : nat;
  ins     : MyListType;
  bpf_m   : Mem.mem;
}.

Definition init_state: state := {|
  ins_len := 0;
  ins     := default_list;
  bpf_m   := Mem.empty;
 |}.


Definition eval_ins_len (st: state): nat := ins_len st.
Definition eval_ins (idx: int) (st: state): int64 := MyListIndexs32 (ins st) idx.

Definition is_dst_R0' (i: int64) : bool := Int.cmpu Ceq (Int.repr (get_dst i)) (Int.repr 0).

Definition is_well_dst' (i: int64) : bool := Int.cmpu Cle (Int.repr (get_dst i)) (Int.repr 10).

Definition is_well_src' (i: int64) : bool := Int.cmpu Cle (Int.repr (get_src i)) (Int.repr 10).

Definition is_well_jump' (pc len: nat) (ofs: int) : bool :=
  Int.cmpu Cle (Int.add (Int.repr (Z.of_nat pc)) ofs) (Int.sub (Int.repr (Z.of_nat len)) (Int.repr 2%Z)).

Definition is_not_div_by_zero' (i: int64) : bool :=
  Int.cmp Cne (get_immediate i) Int.zero.

Definition is_not_div_by_zero64' (i: int64) : bool :=
  Int64.cmp Cne (Int64.repr (Int.signed (get_immediate i))) Int64.zero.

Definition is_shift_range' (i: int64) (upper: int): bool :=
  Int.cmpu Clt (get_immediate i) upper.

Definition is_shift_range64' (i: int64) (upper: int): bool :=
  Int.cmpu Clt (Int.repr (Int64.unsigned (Int64.repr (Int.signed (get_immediate i))))) upper.

Definition nat2int2 (pc len: nat) : int := Int.repr (Z.of_nat (len - 1 - pc)).