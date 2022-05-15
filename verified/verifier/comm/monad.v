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

From compcert Require Import AST Integers Values Memory.

From bpf.comm Require Import BinrBPF Monad.
From bpf.verifier.comm Require Import state.
From Coq Require Import ZArith.

Definition eval_ins_len : M state.state nat := fun st => Some (eval_ins_len st, st).

Definition eval_ins (idx: int) : M state.state int64 := fun st =>
  if (Int.cmpu Clt idx (Int.repr (Z.of_nat (ins_len st)))) then
    Some (eval_ins idx st, st)
  else
    None.