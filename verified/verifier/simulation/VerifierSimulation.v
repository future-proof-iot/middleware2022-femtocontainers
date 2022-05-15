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

(** Definition of matching relation between Coq and C representation *)
From bpf.comm Require Import MemRegion Regs Flag List64.
From compcert Require Import Coqlib Integers Values AST Clight Memory Memtype.

From bpf.clightlogic Require Import Clightlogic.
From bpf.verifier.comm Require Import state.
From Coq Require Import ZArith.
Open Scope Z_scope.

Global Transparent Archi.ptr64.

Definition match_list_ins (m:mem) (b: block) (l: list int64) :=
  forall i, (0 <= i < List.length l)%nat ->
    Mem.loadv AST.Mint64 m  (Vptr b (Ptrofs.repr (8 * (Z.of_nat i)))) = Some (Vlong (List.nth i l Int64.zero)).

Definition match_ins (ins_blk: block) (st: state.state) (m:mem) :=
  List.length (ins st) = (ins_len st) /\
  Z.of_nat (List.length (ins st)) * 8 <= Ptrofs.max_unsigned /\
  match_list_ins m ins_blk (ins st).


Class special_blocks : Type :=
  { st_blk : block;
    ins_blk  : block }.

Section S.

  Context {Blocks : special_blocks}.

  Record match_state  (st: state.state) (m: mem) : Prop :=
    {
      munchange: Mem.unchanged_on (fun b _ => b <> st_blk /\ b <> ins_blk) (bpf_m st) m;
      mins_len : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 0)) = Some (Vint  (Int.repr (Z.of_nat (ins_len st)))) /\ Z.of_nat (ins_len st) >= 1;
      mins     : Mem.loadv AST.Mptr m (Vptr st_blk (Ptrofs.repr 4)) = Some (Vptr ins_blk (Ptrofs.repr 0)) /\ match_ins ins_blk st m;
      mperm    : Mem.range_perm m st_blk 0 8 Cur Freeable /\
                 Mem.range_perm m ins_blk 0 (Z.of_nat (ins_len st)) Cur Readable;
      minvalid : (~Mem.valid_block (bpf_m st) st_blk /\
                  ~Mem.valid_block (bpf_m st) ins_blk) /\
                 (ins_blk <> st_blk) /\
                 (forall b, b <> st_blk /\ b <> ins_blk ->
                  Mem.valid_block m b -> Mem.valid_block (bpf_m st) b);
    }.

End S.

#[global] Notation dcons := (DList.DCons (F:= fun x => x -> Inv state.state)).

Ltac split_conj :=
  match goal with
  | |- ?X <> ?Y /\ _ =>
    split; [intro Hfalse; inversion Hfalse | split_conj]
  | |- ?X <> ?Y =>
    intro Hfalse; inversion Hfalse
  end.
