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

From compcert Require Import Coqlib Integers AST Maps Values Memory Memtype Memdata.
From bpf.model Require Import Semantics.
From bpf.isolation Require Import CommonISOLib.
From Coq Require Import ZArith Lia List.
Import ListNotations.

Open Scope Z_scope.
Definition is_aligned (chunk: memory_chunk) (ofs:Z): Prop := (align_chunk chunk | ofs).
Definition is_well_chunk (chunk: memory_chunk): Prop :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 | Mint64 => True
  | _ => False
  end.

Lemma well_chunk_bool_iff:
  forall chunk st,
    is_well_chunk chunk <-> is_well_chunk_bool chunk st = Some (true, st).
Proof.
  intro chunk.
  unfold is_well_chunk, is_well_chunk_bool.
  split; intro H; destruct chunk; try inversion H; try reflexivity; try apply I.
Qed.

Lemma size_chunk_neq_zero:
  forall chunk, size_chunk chunk <> 0.
Proof.
  intros.
  unfold size_chunk.
  destruct chunk; try lia.
Qed.

Lemma align_chunk_int_range:
  forall chunk, 0 <= align_chunk chunk <= Int.max_unsigned.
Proof.
  unfold align_chunk; intros.
  change Int.max_unsigned with 4294967295.
  destruct chunk; try lia.
Qed.

Lemma align_chunk_gt_zero:
  forall chunk, 0 < align_chunk chunk.
Proof.
  intros.
  unfold align_chunk.
  destruct chunk; try lia.
Qed.

Lemma align_chunk_neq_zero:
  forall chunk, align_chunk chunk <> 0.
Proof.
  intros.
  unfold align_chunk.
  destruct chunk; try lia.
Qed.

Lemma Int_unsigned_repr_chunk:
  forall chunk, Int.unsigned (Int.repr (align_chunk chunk)) = align_chunk chunk.
Proof.
  intro chunk.
  apply (Int.unsigned_repr (align_chunk chunk) (align_chunk_int_range chunk)).
Qed.

Lemma unsigned_repr_size_chunk:
  forall chunk, Int.unsigned (Int.repr (size_chunk chunk)) = size_chunk chunk.
Proof.
  intro chunk.
  apply (Int.unsigned_repr (size_chunk chunk) (size_chunk_int_range chunk)).
Qed.

Lemma well_chunk_implies_size_chunk_align_chunk:
  forall chunk
    (Hwell_chunk: is_well_chunk chunk),
      size_chunk chunk = align_chunk chunk.
Proof.
  intros.
  unfold size_chunk, align_chunk.
  destruct chunk; try inversion Hwell_chunk; reflexivity.
Qed.


Lemma modlu_zero_is_aligned:
  forall chunk ofs, Val.modu (Vint ofs) (Vint (Int.repr (align_chunk chunk))) = Some Vzero ->
    is_aligned chunk (Ptrofs.unsigned (Ptrofs.of_int ofs)).
Proof.
  intros chunk ofs Hmod_eq.
  unfold Val.modu in Hmod_eq.
  destruct (Int.eq _ _) eqn: Heq in Hmod_eq.
  - inversion Hmod_eq.
  - assert (Hsome: forall a b, Some (Vint a) = Some (Vint b) -> a = b).
    + intros a b H1.
      inversion H1; reflexivity.
    + apply Hsome in Hmod_eq.
      unfold is_aligned.
      unfold Int.modu in Hmod_eq.
      rewrite Int_unsigned_repr_chunk in Hmod_eq.
      assert (Hmod: 0<= Int.unsigned ofs mod (align_chunk chunk) < align_chunk chunk).
      apply (Z.mod_pos_bound (Int.unsigned ofs) (align_chunk chunk) (align_chunk_gt_zero chunk)).
      assert (Hmod_max: 0<= Int.unsigned ofs mod (align_chunk chunk) <= Int.max_unsigned).
      assert (Hchun_range: 0 <= align_chunk chunk <= Int.max_unsigned). apply align_chunk_int_range.
      lia.
      assert (H1: Int.unsigned (Int.repr (Int.unsigned ofs mod align_chunk chunk)) = Int.unsigned Int.zero).
      rewrite Hmod_eq; reflexivity.
      apply (Int_repr_zero (Int.unsigned ofs mod align_chunk chunk) Hmod_max) in H1.
      assert (H0: Ptrofs.agree32 (Ptrofs.of_int ofs) ofs). { apply Ptrofs.agree32_of_int. reflexivity. }
      rewrite H0.
      apply (Zmod_divide (Int.unsigned ofs) (align_chunk chunk) (align_chunk_neq_zero chunk) H1).
Qed.

Lemma modu_zero_is_aligned:
  forall chunk ofs
    (Hwell_chunk: is_well_chunk chunk)
    (Hmod_eq: Int.eq Int.zero (Int.modu ofs (Int.repr (size_chunk chunk))) = true),
      (align_chunk chunk | Int.unsigned ofs).
Proof.
  intros.
  apply Int.same_if_eq in Hmod_eq.
  rewrite (well_chunk_implies_size_chunk_align_chunk _ Hwell_chunk) in Hmod_eq.
  unfold Int.modu in Hmod_eq.
  rewrite (Int_unsigned_repr_chunk chunk) in Hmod_eq.
  assert (Hmod: 0<= Int.unsigned ofs mod (align_chunk chunk) < align_chunk chunk).
  apply (Z.mod_pos_bound (Int.unsigned ofs) (align_chunk chunk) (align_chunk_gt_zero chunk)).
  assert (Hmod_max: 0<= Int.unsigned ofs mod (align_chunk chunk) <= Int.max_unsigned).
  assert (Hchun_range: 0 <= align_chunk chunk <= Int.max_unsigned). apply align_chunk_int_range.
  lia.
  assert (H1: Int.unsigned (Int.repr (Int.unsigned ofs mod align_chunk chunk)) = Int.unsigned Int.zero).
  rewrite Hmod_eq; reflexivity.
  apply (Int_repr_zero (Int.unsigned ofs mod align_chunk chunk) Hmod_max) in H1.
  apply (Zmod_divide (Int.unsigned ofs) (align_chunk chunk) (align_chunk_neq_zero chunk) H1).
Qed.

Close Scope Z_scope.