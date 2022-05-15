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
.
Lemma bpf_flag_eq: forall (x y: bpf_flag), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

(** flag_eq: flag -> flag -> bool
  *)
Definition flag_eq (x y: bpf_flag): bool := if bpf_flag_eq x y then true else false.