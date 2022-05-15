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

Definition M (St: Type) (A: Type) := St -> option (A * St).

Definition returnM {A: Type} {St: Type} (a: A) : M St A := fun st => Some (a, st).
Definition errorM {A: Type} {St: Type} : M St A := fun st => None.
Definition bindM {A B: Type} {St: Type} (x: M St A) (f: A -> M St B) : M St B :=
  fun st =>
    match x st with
    | None => None
    | Some (x', st') => (f x') st'
    end.

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.