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

From compcert Require Import AST Integers Memory.

From bpf.comm Require Import State Monad Flag Regs MemRegion rBPFMonadOp.
From bpf.dxcomm Require Import DxIntegers DxValues.
From bpf.dxmodel Require Import DxRegs DxFlag DxMemRegion DxState.

(*
Definition stateM := state. (*This one must be int_64 defined in DxIntegers *)


Definition M (A: Type) := stateM -> option (A * state).

Definition returnM {A: Type} (a: A) : M A := fun st => Some (a, st).
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B :=
  fun st =>
    match x st with
    | None => None
    | Some (x', st') => (f x') st'
    end. *)

Definition M (A: Type) := Monad.M state A.
Definition returnM {A: Type} (a: A) : M A := Monad.returnM a.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B := Monad.bindM x f.

Definition eval_pc: M uint32_t := rBPFMonadOp.eval_pc.
Definition upd_pc (p: uint32_t): M unit := rBPFMonadOp.upd_pc p.
Definition upd_pc_incr: M unit := rBPFMonadOp.upd_pc_incr.

Definition eval_flag: M bpf_flag := rBPFMonadOp.eval_flag.
Definition upd_flag (f:bpf_flag) : M unit := rBPFMonadOp.upd_flag f.

Definition eval_mrs_num: M nat := rBPFMonadOp.eval_mrs_num.

Definition eval_reg (r: reg) : M val64_t := rBPFMonadOp.eval_reg r.
Definition upd_reg (r: reg) (v: val64_t) : M unit := rBPFMonadOp.upd_reg r v.

Definition eval_mrs_regions : M MyMemRegionsType := rBPFMonadOp.eval_mrs_regions.

Definition load_mem (chunk: memory_chunk) (ptr: valu32_t): M val64_t := rBPFMonadOp.load_mem chunk ptr.

Definition store_mem_imm (ptr: valptr8_t) (chunk: memory_chunk) (v: vals32_t) : M unit := rBPFMonadOp.store_mem_imm ptr chunk v.

Definition store_mem_reg (ptr: valptr8_t) (chunk: memory_chunk) (v: val64_t) : M unit := rBPFMonadOp.store_mem_reg ptr chunk v.

Definition eval_ins_len : M uint32_t := rBPFMonadOp.eval_ins_len.

(**r here we must use sint32_t instead of uint32_t because pc is signed int *)
Definition eval_ins (idx: uint32_t) : M int64_t := rBPFMonadOp.eval_ins idx.

Definition cmp_ptr32_nullM (v: valptr8_t): M bool := rBPFMonadOp.cmp_ptr32_nullM v.

Definition int64_to_dst_reg (ins: int64): M reg := int64_to_dst_reg ins.

Definition int64_to_src_reg (ins: int64): M reg := int64_to_src_reg ins.

Definition get_mem_region (n:nat) (mrs: MyMemRegionsType): M memory_region := get_mem_region n mrs.


Declare Scope monad_scope.
Notation "'do' x <-- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.

Definition _bpf_get_call (i: vals32_t) : M valptr8_t := _bpf_get_call i.
Definition exec_function (f: valptr8_t) : M valu32_t := exec_function f.
