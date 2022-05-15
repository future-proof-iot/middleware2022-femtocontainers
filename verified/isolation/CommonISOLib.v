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

From compcert Require Import Coqlib Integers AST Values Memory Ctypes Archi.
From Coq Require Import Lia ZArith.

Open Scope Z_scope.

Lemma size_chunk_gt_zero:
  forall chunk, 0 < size_chunk chunk.
Proof.
  intros.
  unfold size_chunk.
  destruct chunk; try lia.
Qed.

Lemma size_chunk_int_range:
  forall chunk, 0 <= size_chunk chunk <= Int.max_unsigned.
Proof.
  unfold size_chunk; intros.
  change Int.max_unsigned with 4294967295.
  split; destruct chunk; try lia.
Qed.

Lemma Int64_unsigned_ge_0:
  forall v, 0 <= Int64.unsigned v.
Proof.
  intro v.
  assert (Hrange: 0 <= Int64.unsigned v <= Int64.max_unsigned). {
    apply Int64.unsigned_range_2.
  }
  destruct Hrange as [Ha Hb]; assumption.
Qed.

Lemma Int_unsigned_ge_0:
  forall v, 0 <= Int.unsigned v.
Proof.
  intro v.
  assert (Hrange: 0 <= Int.unsigned v <= Int.max_unsigned). {
    apply Int.unsigned_range_2.
  }
  destruct Hrange as [Ha Hb]; assumption.
Qed.

Lemma Int_repr_zero:
  forall v, 0<=v<=Int.max_unsigned -> Int.unsigned (Int.repr v) = Int.unsigned (Int.zero) -> v = 0.
Proof.
  intros.
  rewrite (Int.unsigned_repr v H) in H0.
  rewrite Int.unsigned_zero in H0.
  assumption.
Qed.

Lemma Ptrofs_of_int_unsigned:
  forall v, Ptrofs.unsigned (Ptrofs.of_int v) = Int.unsigned v.
Proof.
  intros.
  assert (H1: Ptrofs.agree32 (Ptrofs.of_int v) v). { apply Ptrofs.agree32_of_int. reflexivity. }
  rewrite H1; reflexivity.
Qed.

Lemma ptrofs_unsigned_ge_0:
  forall v, 0 <= Ptrofs.unsigned v.
Proof.
  intro v.
  assert (Hrange: 0 <= Ptrofs.unsigned v <= Ptrofs.max_unsigned). {
    apply Ptrofs.unsigned_range_2.
  }
  destruct Hrange as [Ha Hb]; assumption.
Qed.

Lemma Cle_Zle_iff:
  forall lo ofs,
    negb (Int.ltu ofs lo) = true <-> Int.unsigned lo <= Int.unsigned ofs.
Proof.
  split; intros.
  - rewrite negb_true_iff in H.
    unfold Int.ltu in H.
    destruct (zlt _ _) in H; try inversion H.
    lia.
  - rewrite negb_true_iff.
    unfold Int.ltu.
    apply zlt_false.
    lia.
Qed.

Lemma Clt_Zlt_iff:
  forall ofs hi,
    Int.ltu ofs hi = true <->
      Int.unsigned ofs < Int.unsigned hi.
Proof.
  split; intros.
  - unfold Int.ltu in H.
    destruct (zlt _ _) in H; try inversion H.
    lia.
  - unfold Int.ltu.
    apply zlt_true.
    assumption.
Qed.

Lemma Int64_unsigned_size_chunk_ge_0:
  forall ofs chunk,
    0 <= Int64.unsigned ofs + size_chunk chunk.
Proof.
  intros.
  assert (Hchunk_lo: 0 < size_chunk chunk). apply size_chunk_gt_zero.
  assert (Hofs_lo: 0<= Int64.unsigned ofs). apply Int64_unsigned_ge_0. 
  unfold size_chunk; destruct chunk; rewrite Z.add_comm; try lia.
Qed.

Lemma Int_unsigned_size_chunk_ge_0:
  forall ofs chunk,
    0 <= Int.unsigned ofs + size_chunk chunk.
Proof.
  intros.
  assert (Hchunk_lo: 0 < size_chunk chunk). apply size_chunk_gt_zero.
  assert (Hofs_lo: 0<= Int.unsigned ofs). apply Int_unsigned_ge_0.
  unfold size_chunk; destruct chunk; rewrite Z.add_comm; try lia.
Qed.

Lemma Int64_unsigned_ofs_size_chunk_ge_0:
  forall ofs chunk,
    Int64.unsigned ofs < Int64.unsigned ofs + size_chunk chunk.
Proof.
  intros.
  assert (Hchunk_lo: 0 < size_chunk chunk). apply size_chunk_gt_zero.
  assert (Hofs_lo: 0<= Int64.unsigned ofs). apply Int64_unsigned_ge_0. 
  lia.
Qed.

Lemma Int_unsigned_ofs_size_chunk_ge_0:
  forall ofs chunk,
    Int.unsigned ofs < Int.unsigned ofs + size_chunk chunk.
Proof.
  intros.
  assert (Hchunk_lo: 0 < size_chunk chunk). apply size_chunk_gt_zero.
  assert (Hofs_lo: 0<= Int.unsigned ofs). apply Int_unsigned_ge_0.
  lia.
Qed.

(**r Here is a problem, 'ofs+size_chunk':Z may be greater than Int64.mex_unsigned! 
     While the 'Vlong (Int64.repr (ofs+size_chunk))': Val is always within the range!
 *)

Lemma hi_ofs_max_unsigned:
  forall ofs chunk,
    negb
         (Int.ltu (Int.repr (Int.max_unsigned-(size_chunk chunk))) ofs) = true ->
      0 <= Int.unsigned ofs + size_chunk chunk <= Int.max_unsigned.
Proof.
  intros ofs chunk Hcmp.
  change Int.max_unsigned with 4294967295 in *.
  remember ((Int.ltu (Int.repr (4294967295 - size_chunk chunk))) ofs) as k eqn: Hk.
  rewrite Hk in Hcmp; clear Hk.
  rewrite negb_true_iff in Hcmp.
  unfold Int.ltu in Hcmp.
  destruct (zlt _ _) in Hcmp.
  - inversion Hcmp.
  - clear Hcmp.
    assert (Heq_max: 0 <= 4294967295 - size_chunk chunk <= 4294967295). {
      unfold size_chunk; destruct chunk; try lia.
    }
    rewrite (Int.unsigned_repr _ Heq_max) in g.
    split.
    apply Int_unsigned_size_chunk_ge_0.
    lia.
Qed.

Lemma Clt_implies_Zlt_add:
  forall ofs chunk hi, Int.ltu (Int.add ofs (Int.repr (size_chunk chunk))) hi = true ->
    0 <= (Int.unsigned ofs + size_chunk chunk) <= Int.max_unsigned ->
      0<= Int.unsigned ofs + (size_chunk chunk) < Int.unsigned hi.
Proof.
  intros.
  split.
  apply Int_unsigned_size_chunk_ge_0.
  unfold Int.ltu, Int.add in H.
  destruct (zlt _ _) in H; try inversion H.
  assert (H5: Int.unsigned (Int.repr (size_chunk chunk)) = size_chunk chunk). { apply Int.unsigned_repr; apply size_chunk_int_range; assumption. }
  rewrite H5 in l.
  assert (H6: Int.unsigned (Int.repr (Int.unsigned ofs + size_chunk chunk)) = 
              (Int.unsigned ofs + size_chunk chunk)). { apply Int.unsigned_repr; assumption. }
  rewrite H6 in l; assumption.
Qed.

Close Scope Z_scope.