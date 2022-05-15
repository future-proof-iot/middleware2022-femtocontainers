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

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.lib Require Integers.

Definition C_U8  := Ctypes.Tint Ctypes.I8  Ctypes.Unsigned Ctypes.noattr.

Definition C_U16 := Ctypes.Tint Ctypes.I16 Ctypes.Unsigned Ctypes.noattr.

Definition C_U32 := Ctypes.Tint Ctypes.I32 Ctypes.Unsigned Ctypes.noattr.

Definition C_U64 := Ctypes.Tlong Ctypes.Unsigned Ctypes.noattr.

Definition C_S8  := Ctypes.Tint Ctypes.I8  Ctypes.Signed Ctypes.noattr.

Definition C_S16 := Ctypes.Tint Ctypes.I16 Ctypes.Signed Ctypes.noattr.

Definition C_S32 := Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr.

Definition C_S64 := Ctypes.Tlong Ctypes.Signed Ctypes.noattr.

Definition C_U8_pointer  := Ctypes.Tpointer C_U8  Ctypes.noattr.

Definition C_U16_pointer := Ctypes.Tpointer C_U16 Ctypes.noattr.

Definition C_U32_pointer := Ctypes.Tpointer C_U32 Ctypes.noattr.

Definition C_U64_pointer := Ctypes.Tpointer C_U64 Ctypes.noattr.

Definition C_S8_pointer  := Ctypes.Tpointer C_S8  Ctypes.noattr.

Definition C_S16_pointer := Ctypes.Tpointer C_S16 Ctypes.noattr.

Definition C_S32_pointer := Ctypes.Tpointer C_S32 Ctypes.noattr.

Definition C_S64_pointer := Ctypes.Tpointer C_S64 Ctypes.noattr.
(*
Definition C_Func_pointer := Ctypes.Tpointer (Tfunction
                            (Tcons (tptr (Tstruct _bpf_state noattr))
                              (Tcons tuint Tnil)) tulong cc_default) Ctypes.noattr. *)

(******************** C_U32 operations *******************)

Definition C_U32_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_U32.

Definition C_U32_add (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U32.

Definition C_U32_sub (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U32.

Definition C_U32_mul (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Omul x y C_U32.

Definition C_U32_div (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Odiv x y C_U32.

Definition C_U32_mod (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Omod x y C_U32.

Definition C_U32_and (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oand x y C_U32.

Definition C_U32_or (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oor x y C_U32.

Definition C_U32_xor (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oxor x y C_U32.

Definition C_U32_shl (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oshl x y C_U32.

Definition C_U32_shr (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oshr x y C_U32.

Definition C_U32_eq (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oeq x y C_U32.

Definition C_U32_ne (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.One x y C_U32.

Definition C_U32_lt (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Olt x y C_U32.

Definition C_U32_gt (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Ogt x y C_U32.

Definition C_U32_le (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Ole x y C_U32.

Definition C_U32_ge (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oge x y C_U32.

(******************** C_U64 operations *******************)

Definition C_U64_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_U64.

Definition C_U64_add (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U64.

Definition C_U64_sub (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U64.

Definition C_U64_mul (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Omul x y C_U64.

Definition C_U64_div (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Odiv x y C_U64.

Definition C_U64_mod (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Omod x y C_U64.

Definition C_U64_and (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oand x y C_U64.

Definition C_U64_or (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oor x y C_U64.

Definition C_U64_xor (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oxor x y C_U64.

Definition C_U64_shl (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oshl x y C_U64.

Definition C_U64_shr (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oshr x y C_U64.

Definition C_U64_eq (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oeq x y C_U64.

Definition C_U64_ne (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.One x y C_U64.

Definition C_U64_lt (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Olt x y C_U64.

Definition C_U64_gt (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Ogt x y C_U64.

Definition C_U64_le (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Ole x y C_U64.

Definition C_U64_ge (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oge x y C_U64.