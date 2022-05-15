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

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

From bpf.comm Require Import State.
From bpf.dxcomm Require Import CoqIntegers DxIntegers DxValues DxList64.
From bpf.dxmodel Require Import IdentDef DxFlag DxRegs DxMemRegion.

From Coq Require Import List ZArith.
Import ListNotations.

(******************** Dx Related *******************)

(** Coq2C: state -> 
            struct state {
              unsigned int pc;
              unsigned long long regmap[11];
            };
  *)

Definition state_struct_type: Ctypes.type := Ctypes.Tstruct state_id Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(pc_id, C_U32); (flag_id, C_S32); (regmaps_id, C_regmap); (mem_num_id, C_U32); (mem_regs_id, mem_region_type); (ins_len_id, C_U32); (ins_id, C_U64_pointer)] Ctypes.noattr.

Definition stateCompilableType := MkCompilableType state state_struct_type.

Module Exports.
  Definition stateCompilableType := stateCompilableType.
End Exports.
