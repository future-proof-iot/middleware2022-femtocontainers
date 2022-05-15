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

From bpf.dxcomm Require Import DxIntegers.

From bpf.comm Require Import Monad.
From bpf.verifier.comm Require Import state monad.

Definition M (A: Type) := M state.state A.

Definition returnM {A: Type} (a: A) : M A := returnM a.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B := bindM x f.

Definition eval_ins_len : M nat := monad.eval_ins_len.

Definition eval_ins (idx: uint32_t) : M int64_t := monad.eval_ins idx.

Declare Scope monad_scope.
Notation "'do' x <-- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.