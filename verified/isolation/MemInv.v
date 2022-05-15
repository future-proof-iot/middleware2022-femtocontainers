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
From bpf.comm Require Import MemRegion State.
From bpf.model Require Import Semantics.
From bpf.isolation Require Import AlignChunk.
From Coq Require Import ZArith Lia List.
Import ListNotations.

Open Scope Z_scope.

Definition is_byte_memval (mv: memval): Prop :=
  match mv with
  | Byte b => True
  | _ => False
  end.

Definition is_byte_block (b:block) (m:mem): Prop := 
  forall o,
      Mem.perm m b o Cur Readable ->
      is_byte_memval (ZMap.get o ((Mem.mem_contents m) !! b)). (**r Notation "a !! b" := (PMap.get b a) *)

Lemma is_byte_memval_iff:
  forall mv,
    is_byte_memval mv <-> exists b, mv = Byte b.
Proof.
  unfold is_byte_memval; split; intros.
  - destruct mv; try intuition.
    exists i; reflexivity.
  - destruct H as (b & H).
    rewrite H.
    constructor.
Qed.

Definition inv_memory_region (m:mem) (mr: memory_region): Prop :=
  exists b,
    (block_ptr mr) = Vptr b Ptrofs.zero /\ Mem.valid_block m b /\ is_byte_block b m /\
    exists base len,
      start_addr mr = Vint base /\ block_size mr = Vint len /\
      perm_order (block_perm mr) Readable /\
      Mem.range_perm m b 0 (Int.unsigned len) Cur (block_perm mr).

(**TODO: exists start_blk, ... *)
Fixpoint disjoint_blocks (n:nat) (mrs: list memory_region): Prop :=
  match mrs with
  | [] => True
  | hd :: tl => Vptr (Pos.of_nat n) Ptrofs.zero = block_ptr hd /\ disjoint_blocks (n+1) tl
  end.

Fixpoint inv_memory_regions (m:mem) (mrs: list memory_region): Prop :=
  match mrs with
  | [] => True
  | hd :: tl => inv_memory_region m hd /\ inv_memory_regions m tl
  end.

Lemma In_inv_memory_regions:
  forall mr m l,
    List.In mr l -> inv_memory_regions m l ->
      inv_memory_region m mr.
Proof.
  intros.
  induction l;
  simpl in *.
  inversion H.
  destruct H.
  - subst. intuition.
  - apply IHl.
    assumption.
    intuition.
Qed.

Definition memory_inv (st: state): Prop :=
  (1 <= mrs_num st)%nat /\
  List.length (bpf_mrs st) = mrs_num st /\
  (exists start_blk,
    disjoint_blocks start_blk (bpf_mrs st)) /\
  inv_memory_regions (bpf_m st) (bpf_mrs st).

Fixpoint is_byte_list_memval (l: list memval): Prop :=
  match l with
  | nil => True
  | hd :: tl => is_byte_memval hd /\ is_byte_list_memval tl
  end.

Lemma memval_proj_bytes_some:
    forall l, is_byte_list_memval l ->
      exists lb, proj_bytes l = Some lb.
Proof.
  intros l H.
  unfold proj_bytes.
  induction l.
  - exists nil; reflexivity.
  - simpl in H.
    destruct H.
    apply (is_byte_memval_iff _) in H; destruct H.
    rewrite H.
    apply IHl in H0; destruct H0.
    rewrite H0.
    exists (x::x0); reflexivity.
Qed.

Definition is_vlong_or_vint (v: val): Prop :=
  match v with
  | Vlong _ | Vint _ => True
  | _ => False
  end.

Lemma is_vlong_or_vint_iff_some:
  forall v, is_vlong_or_vint v <->
    (exists vl, v = Vlong vl) \/ exists vi, v = Vint vi.
Proof.
  split; intros.
  - destruct v; try inversion H.
    + right; exists i; reflexivity.
    + left; exists i; reflexivity.
  - do 2 destruct H; rewrite H; apply I.
Qed.

Lemma decode_val_byte_some_vlong_or_vint:
  forall chunk l,
    is_well_chunk chunk -> 
    is_byte_list_memval l ->
      (exists vl, decode_val chunk l = Vlong vl) \/ (exists vi, decode_val chunk l = Vint vi).
Proof.
  intros chunk l IWC IBLM.
  unfold decode_val.
  apply memval_proj_bytes_some in IBLM; destruct IBLM.
  rewrite H.
  destruct chunk; simpl in IWC; try contradiction.
  - right; exists (Int.zero_ext 8 (Int.repr (decode_int x))); reflexivity.
  - right; exists (Int.zero_ext 16 (Int.repr (decode_int x))); reflexivity.
  - right; exists (Int.repr (decode_int x)); reflexivity.
  - left;  exists (Int64.repr (decode_int x)); reflexivity.
Qed.

Lemma inv_memory_region_freeable_implies_is_byte_memval:
  forall b m lo hi, 
    Mem.range_perm m b lo hi Cur Readable ->
    is_byte_block b m ->
     forall ofs, lo <= ofs < hi -> is_byte_memval (ZMap.get ofs (Mem.mem_contents m) !! b).
Proof.
  unfold is_byte_block.
  intros.
  apply (H0 ofs) in H; try assumption.
Qed.

Lemma getN_byte_list_memval:
  forall chunk m b lo hi, 
    Mem.range_perm m b lo hi Cur Readable -> 
    is_byte_block b m -> 
    is_well_chunk chunk ->
      forall ofs, lo <= ofs /\ ofs + (size_chunk chunk) < hi -> is_byte_list_memval (Mem.getN (size_chunk_nat chunk) ofs ((Mem.mem_contents m) !! b)).
Proof. 
  intro chunk.
  assert (Ha: forall x y z n, x <= y /\ y + (size_chunk chunk) < z -> 0 <=n <= (size_chunk chunk) -> x <= y+n < z). {
    intros x y z n H0 H1.
    unfold size_chunk in *; destruct chunk; try lia.
  }
  intros m b lo hi H0 H1 H2.
  assert (Hb: forall ofs, lo <= ofs < hi -> is_byte_memval (ZMap.get ofs (Mem.mem_contents m) !! b)). {
    apply (inv_memory_region_freeable_implies_is_byte_memval _ _ _ _); assumption.
  }
  unfold size_chunk_nat, size_chunk.
  destruct chunk eqn:k in H2; try contradiction; subst; simpl; simpl in *; unfold is_byte_list_memval, Mem.getN; intros ofs H3.
  - split; try (apply I).
    apply (Hb _); assert (H4: lo <= ofs + 0 < hi -> lo <= ofs < hi); try lia.
  - split.
    apply (Hb _); assert (H4: lo <= ofs + 0 < hi -> lo <= ofs < hi); try lia.
    split; try (apply I).
    apply (Hb _); apply (Ha _ _ _ 1); lia.
  - split.
    apply (Hb _); assert (H4: lo <= ofs + 0 < hi -> lo <= ofs < hi); try lia.
    split.
    apply (Hb _); apply (Ha _ _ _ 1); lia.
    split.
    apply (Hb _); assert (H4: lo <= ofs + 2 < hi -> lo <= ofs+1+1 < hi); try lia.
    split;try (apply I).
    apply (Hb _); assert (H4: lo <= ofs + 3 < hi -> lo <= ofs+1+1+1 < hi); try lia.
  - split.
    apply (Hb _); assert (H4: lo <= ofs + 0 < hi -> lo <= ofs < hi); try lia.
    split.
    apply (Hb _); apply (Ha _ _ _ 1); lia.
    split.
    apply (Hb _); assert (H4: lo <= ofs + 2 < hi -> lo <= ofs+1+1 < hi); try lia.
    split.
    apply (Hb _); assert (H4: lo <= ofs + 3 < hi -> lo <= ofs+1+1+1 < hi); try lia.
    split.
    apply (Hb _); assert (H4: lo <= ofs + 4 < hi -> lo <= ofs+1+1+1+1 < hi); try lia.
    split.
    apply (Hb _); assert (H4: lo <= ofs + 5 < hi -> lo <= ofs+1+1+1+1+1 < hi); try lia.
    split.
    apply (Hb _);
    assert (H4: lo <= ofs + 6 < hi -> lo <= ofs+1+1+1+1+1+1 < hi); try lia.
    split.
    apply (Hb _);
    assert (H4: lo <= ofs + 7 < hi -> lo <= ofs+1+1+1+1+1+1+1 < hi); try lia.
    split;try (apply I).
Qed.

Lemma load_some_well_chunk_vlong_or_vint:
  forall m mr chunk b ofs v len,
    inv_memory_region m mr ->
    block_ptr mr = Vptr b Ptrofs.zero ->
    block_size mr = Vint len ->
    is_well_chunk chunk ->
    0 <= ofs /\ ofs + size_chunk chunk < Int.unsigned len ->
    Mem.load chunk m b ofs = Some v ->
      is_vlong_or_vint v.
Proof.
  Transparent Mem.load.
  unfold Mem.load.
  intros m mr chunk b ofs v len IMR Hptr Hsize IWC Hrange Hload.
  destruct IMR as [bi [Hi1 [Hi2 [Hi3 [basei [leni [Hi4 [Hi5 [Hpermi Hi6]]]]]]]]].
  rewrite Hi1 in Hptr; inversion Hptr; subst.
  rewrite Hi5 in Hsize; inversion Hsize; subst.
  assert (HpermReadable: Mem.range_perm m b 0 (Int.unsigned len) Cur Readable). {
    eapply Mem.range_perm_implies; eauto.
  }

  unfold inv_memory_region in Hload.
  destruct (Mem.valid_access_dec _ _ _ _ _) in Hload.
  - assert (Hiblm: forall o, 
      0%Z <= o /\ o + (size_chunk chunk) < Int.unsigned len ->
      is_byte_list_memval (Mem.getN (size_chunk_nat chunk) o ((Mem.mem_contents m) !! b))). {
        apply (getN_byte_list_memval _ _ _ _ _ HpermReadable Hi3 IWC).
    }
    apply (Hiblm _) in Hrange.
    inversion Hload.
    rewrite -> H0 in *.
    set (l := Mem.getN (size_chunk_nat chunk) ofs (Mem.mem_contents m) !! b).
    assert (Hdecode: (exists vl, v = Vlong vl) \/ (exists vi, v = Vint vi)). {
      rewrite <- H0.
      apply (decode_val_byte_some_vlong_or_vint _ _ IWC Hrange).
    }
    rewrite -> is_vlong_or_vint_iff_some; assumption.
  - inversion Hload.
Qed.

Lemma range_perm_included:
  forall m b p lo hi ofs_lo ofs_hi, 
    lo <= ofs_lo -> ofs_lo < ofs_hi -> ofs_hi < hi -> 
    Mem.range_perm m b lo hi Cur p ->
      Mem.range_perm m b ofs_lo ofs_hi Cur p.
Proof.
  intros.
  apply (Mem.range_perm_implies _ _ _ _ _ p _). 2:{ constructor. }
  unfold Mem.range_perm in *; intros.
  apply H2.
  lia.
Qed.

(** Store operations *)

Lemma inj_bytes_is_byte_list_memval:
  forall bl,
    is_byte_list_memval (inj_bytes bl).
Proof.
  unfold is_byte_list_memval, is_byte_memval.
  induction bl.
  - simpl. apply I.
  - simpl.
    split; try (apply I).
    assumption.
Qed.

Lemma encode_val_is_byte_list_memval:
  forall chunk v src
    (Hwell_chunk: is_well_chunk chunk)
    (Hvlong: exists vl, v = Vlong vl)
    (Hvint_vlong: vlong_to_vint_or_vlong chunk v = src),
    is_byte_list_memval (encode_val chunk src).
Proof.
  unfold vlong_to_vint_or_vlong.
  intros.
  destruct Hvlong as [vl Hvlong].
  rewrite -> Hvlong in Hvint_vlong.
  destruct chunk in *; try inversion Hwell_chunk; rewrite <- Hvint_vlong; simpl; try apply (inj_bytes_is_byte_list_memval _).
Qed.

Lemma encode_val_is_byte_list_memval_vint:
  forall chunk v src
    (Hwell_chunk: is_well_chunk chunk)
    (Hvint: exists vi, v = Vint vi)
    (Hvint_vlong: vint_to_vint_or_vlong chunk v = src),
    is_byte_list_memval (encode_val chunk src).
Proof.
  unfold vint_to_vint_or_vlong.
  intros.
  destruct Hvint as [vl Hvint].
  rewrite -> Hvint in Hvint_vlong.
  destruct chunk in *; try inversion Hwell_chunk; rewrite <- Hvint_vlong; simpl; try apply (inj_bytes_is_byte_list_memval _).
Qed.

Lemma setN_other_is_byte_list_memval:
  forall vl c p q,
    is_byte_list_memval vl ->
    is_byte_memval (ZMap.get q c) ->
    p <= q < p + Z_of_nat (length vl) ->
      is_byte_memval (ZMap.get q (Mem.setN vl p c)).
Proof.
  induction vl; intros; unfold is_byte_list_memval, is_byte_memval in *; simpl.
  - assumption.
  - destruct (zeq p q).
    + subst q.
      rewrite Mem.setN_outside.
      * rewrite ZMap.gss.
        destruct H as [Ha H]; assumption.
      * left; lia.
    + apply IHvl.
      * destruct H as [Ha H]; assumption.
      * rewrite ZMap.gso.
        assumption.
        lia.
      * simpl length in H1; rewrite inj_S in H1.
        lia.
Qed.

Lemma get_setN_is_byte_list_memval:
  forall vl c p q,
    is_byte_list_memval vl ->
    is_byte_memval (ZMap.get q c) ->
    ~(p <= q < p + Z_of_nat (length vl)) ->
      is_byte_memval (ZMap.get q (Mem.setN vl p c)).
Proof.
  intros; unfold is_byte_list_memval, is_byte_memval in *; simpl.
  destruct (zle p q).
  destruct (zlt q (p + Z.of_nat (length vl))).
  - apply (setN_other_is_byte_list_memval _ _ _ _ H H0).
    split; assumption.
  - rewrite Mem.setN_outside.
    assumption.
    right; assumption.
  - rewrite Mem.setN_outside.
    assumption.
    left; lia.
Qed.


Lemma setN_is_byte_list_memval:
  forall vl c p q,
    is_byte_list_memval vl ->
    is_byte_memval (ZMap.get q c) ->
      is_byte_memval (ZMap.get q (Mem.setN vl p c)).
Proof.
  intros.
  destruct (zle p q).
  destruct (zlt q (p + Z_of_nat (length vl))).
  - apply (setN_other_is_byte_list_memval _ _ _ _ H H0).
    split; assumption.
  - apply (get_setN_is_byte_list_memval _ _ _ _ H H0).
    lia.
  - apply (get_setN_is_byte_list_memval _ _ _ _ H H0).
    lia.
Qed.

Lemma store_is_byte_block:
  forall chunk m1 blk ofs v m2
    (Hwell_chunk: is_well_chunk chunk)
    (Hvlong: exists vl, v = Vlong vl)
    (Hstore: Mem.store chunk m1 blk ofs (vlong_to_vint_or_vlong chunk v) = Some m2)
    (His_byte: is_byte_block blk m1),
      is_byte_block blk m2.
Proof.
  intros.
  unfold is_byte_block.
  intros o Hperm.
  apply (Mem.perm_store_2 _ _ _ _ _ _ Hstore) in Hperm.
  apply His_byte in Hperm.
  
  Transparent Mem.store.
  unfold Mem.store in Hstore.
  destruct (Mem.valid_access_dec _ _ _ _ _) in Hstore. 2:{ inversion Hstore. }
  inversion Hstore; clear Hstore H0.
  simpl.

  assert (His_byte_list: is_byte_list_memval (encode_val chunk (vlong_to_vint_or_vlong chunk v))). {
    apply (encode_val_is_byte_list_memval _ _ _ Hwell_chunk Hvlong); reflexivity.
  }
  rewrite PMap.gss.
  apply (setN_is_byte_list_memval _ _ _ _ His_byte_list Hperm).
Qed.

Lemma store_is_byte_block_vint:
  forall chunk m1 blk ofs v m2
    (Hwell_chunk: is_well_chunk chunk)
    (HVint: exists vi, v = Vint vi)
    (Hstore: Mem.store chunk m1 blk ofs (vint_to_vint_or_vlong chunk v) = Some m2)
    (His_byte: is_byte_block blk m1),
      is_byte_block blk m2.
Proof.
  intros.
  unfold is_byte_block.
  intros o Hperm.
  apply (Mem.perm_store_2 _ _ _ _ _ _ Hstore) in Hperm.
  apply His_byte in Hperm.
  
  Transparent Mem.store.
  unfold Mem.store in Hstore.
  destruct (Mem.valid_access_dec _ _ _ _ _) in Hstore. 2:{ inversion Hstore. }
  inversion Hstore; clear Hstore H0.
  simpl.

  assert (His_byte_list: is_byte_list_memval (encode_val chunk (vint_to_vint_or_vlong chunk v))). {
    apply (encode_val_is_byte_list_memval_vint _ _ _ Hwell_chunk HVint); reflexivity.
  }
  rewrite PMap.gss.
  apply (setN_is_byte_list_memval _ _ _ _ His_byte_list Hperm).
Qed.

Lemma store_is_byte_block_disjoint:
  forall chunk m1 m2 b1 b2 ofs v,
    is_byte_list_memval (encode_val chunk v) ->
    Mem.store chunk m1 b1 ofs v = Some m2 ->
    b1 <> b2 ->
    is_byte_block b1 m1 ->
    is_byte_block b2 m1 ->
      is_byte_block b2 m2.
Proof.
  unfold is_byte_block.
  intros.
  assert (H5:= H0).
  unfold Mem.store in H0.
  destruct (Mem.valid_access_dec _ _ _ _ _); try inversion H0.
  simpl.
  rewrite PMap.gso. 2:{ lia. }
  apply H3.
  apply (Mem.perm_store_2 _ _ _ _ _ _ H5).
  assumption.
Qed.

Lemma store_is_region_freeable_disjoint:
  forall chunk m1 m2 b1 b2 ofs v lo_1 hi_1 lo_2 hi_2 p,
    is_byte_list_memval (encode_val chunk v) ->
    Mem.store chunk m1 b1 ofs v = Some m2 ->
    b1 <> b2 ->
    Mem.range_perm m1 b1 lo_1 hi_1 Cur p ->
    Mem.range_perm m1 b2 lo_2 hi_2 Cur p ->
      Mem.range_perm m2 b2 lo_2 hi_2 Cur p.
Proof.
  unfold Mem.range_perm.
  intros.
  apply H3 in H4.
  apply (Mem.perm_store_1 _ _ _ _ _ _ H0 _ _ _ _ H4).
Qed.

Lemma store_memory_region_including:
  forall m1 m2 mr1 mr2 b1 b2 len1 len2 chunk ofs v,
    inv_memory_region m1 mr1 ->
    block_ptr mr1 = Vptr b1 Ptrofs.zero ->
    block_size mr1 = Vint len1 ->
    inv_memory_region m1 mr2 ->
    block_ptr mr2 = Vptr b2 Ptrofs.zero ->
    block_size mr2 = Vint len2 ->
    b1 <> b2 ->
    Mem.store chunk m1 b1 ofs v = Some m2 ->
    is_byte_list_memval (encode_val chunk v) ->
    inv_memory_region m2 mr2.
Proof.
  intros.
  destruct H as [blk1 [Hptr1 [Hvalid_blk1 [Hbyte1 [start1 [len_1 [Haddr1 [Hlen1 Hperm1]]]]]]]].
  rewrite Hptr1 in H0; inversion H0; subst blk1; clear H0.
  rewrite Hlen1 in H1; inversion H1; subst len_1; clear H1.
  
  destruct H2 as [blk2 [Hptr2 [Hvalid_blk2 [Hbyte2 [start2 [len_2 [Haddr2 [Hlen2 Hperm2]]]]]]]].
  rewrite Hptr2 in H3; inversion H3; subst blk2; clear H3.
  rewrite Hlen2 in H4; inversion H4; subst len_2; clear H4.

  unfold inv_memory_region.
  exists b2.
  split; try assumption.
  split.
  apply (Mem.store_valid_block_1 _ _ _ _ _ _ H6 _ Hvalid_blk2).
  split.
  apply (store_is_byte_block_disjoint _ _ _ _ _ _ _ H7 H6 H5 Hbyte1 Hbyte2).
  exists start2, len2.
  split; try assumption.
  split; try assumption.
  unfold Mem.range_perm in *.
  split; [intuition | idtac].
  intros ofs0 Hofs0_range.
  apply Hperm2 in Hofs0_range.
  apply (Mem.perm_store_1 _ _ _ _ _ _ H6); assumption.
Qed.



(*
Definition inv_memory_regions_state (st: state) := inv_memory_regions (eval_mem st) (eval_mem_regions st). *)

(** alu: upd_reg wiil never have effect on memory and memory regions *)
Lemma mem_inv_upd_reg_mem:
  forall st1 st2 r n
    (Halu: upd_reg r (Vlong n) st1 = st2),
      eval_mem st1 = eval_mem st2.
Proof.
  unfold upd_reg, eval_mem; intros.
  inversion Halu.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_reg_memregions:
  forall st1 st2 r n
    (Halu: upd_reg r (Vlong n) st1 = st2),
      eval_mem_regions st1 = eval_mem_regions st2.
Proof.
  unfold upd_reg, eval_mem_regions; intros.
  inversion Halu.
  simpl; reflexivity.
Qed.

(** alu: upd_flag wiil have no effect on memory and memory regions *)
Lemma mem_inv_upd_flag_mem:
  forall st1 st2 f
    (Halu: upd_flag f st1 = st2),
      eval_mem st1 = eval_mem st2.
Proof.
  unfold upd_flag, eval_mem; intros.
  inversion Halu.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_flag_memregions:
  forall st1 st2 f
    (Halu: upd_flag f st1 = st2),
      eval_mem_regions st1 = eval_mem_regions st2.
Proof.
  unfold upd_flag, eval_mem_regions; intros.
  inversion Halu.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_mem_mem:
  forall st1 st2 m
    (Hmem: upd_mem m st1 = st2),
      eval_mem st2 = m.
Proof.
  unfold upd_mem, eval_mem; intros.
  inversion Hmem.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_mem_memregions:
  forall st1 st2 m
    (Hmem: upd_mem m st1 = st2),
      eval_mem_regions st1 = eval_mem_regions st2.
Proof.
  unfold upd_mem, eval_mem_regions; intros.
  inversion Hmem.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_pc_incr_mem:
  forall st1 st2
    (Hpc: upd_pc_incr st1 = st2),
      eval_mem st1 = eval_mem st2.
Proof.
  unfold upd_pc_incr, eval_mem; intros.
  inversion Hpc.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_pc_incr_memregions:
  forall st1 st2
    (Hpc: upd_pc_incr st1 = st2),
      eval_mem_regions st1 = eval_mem_regions st2.
Proof.
  unfold upd_pc_incr, eval_mem_regions; intros.
  inversion Hpc.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_pc_mem:
  forall st1 st2 p
    (Hpc: upd_pc p st1 = st2),
      eval_mem st1 = eval_mem st2.
Proof.
  unfold upd_pc, eval_mem; intros.
  inversion Hpc.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_pc_memregions:
  forall st1 st2 p
    (Hpc: upd_pc p st1 = st2),
      eval_mem_regions st1 = eval_mem_regions st2.
Proof.
  unfold upd_pc, eval_mem_regions; intros.
  inversion Hpc.
  simpl; reflexivity.
Qed.

Lemma mem_inv_upd_reg:
  forall st1 st2 r n
    (Hmem_inv: memory_inv st1)
    (Halu: upd_reg r (Vlong n) st1 = st2),
      memory_inv st2.
Proof.
  unfold memory_inv, upd_reg.
  intros.
  rewrite <- Halu.
  simpl.
  assumption.
Qed.

Lemma mem_inv_upd_flag:
  forall st1 st2 f
    (Hmem_inv: memory_inv st1)
    (Hflag: upd_flag f st1 = st2),
      memory_inv st2.
Proof.
  unfold memory_inv, upd_flag.
  intros.
  rewrite <- Hflag.
  simpl.
  assumption.
Qed.

Lemma Mem_range_perm_store:
  forall m m0 b b0 lo hi k p chunk i v
  (Hrange_perm : Mem.range_perm m0 b0 lo hi k p)
  (Hstore : Mem.store chunk m0 b i v = Some m),
    Mem.range_perm m b0 lo hi k p.
Proof.
  unfold Mem.range_perm.
  intros.
  eapply Mem.perm_store_1; eauto.
Qed.

Lemma mem_inv_store_mem_regions_vlong:
  forall m m0 chunk l b i vl
    (Hwell_chunk: is_well_chunk chunk)
    (Hmem_inv : inv_memory_regions m0 l)
    (Hstore: Mem.store chunk m0 b (Ptrofs.unsigned i) (vlong_to_vint_or_vlong chunk (Vlong vl)) = Some m),
      inv_memory_regions m l.
Proof.
  induction l.
  simpl; intros.
  constructor.

  simpl; intros.
  destruct Hmem_inv as (Hmem_inv_mr & Hmem_inv_mrs).
  split.
  -
    unfold inv_memory_region in *.
    destruct Hmem_inv_mr as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstart & Hsize & Hperm & Hrange_perm).
    exists b0.
    repeat (split; [try assumption | idtac]).
    + eapply Mem.store_valid_block_1; eauto.
    + destruct ((b =? b0)%positive) eqn: Hb_eq.
      * rewrite Pos.eqb_eq in Hb_eq.
        subst.
        eapply store_is_byte_block; eauto.
      * rewrite Pos.eqb_neq in Hb_eq.
        unfold is_byte_block in *.
        erewrite Mem.store_mem_contents; eauto.
        erewrite PMap.gso; eauto.
        intros.
        apply Hbyte.
        eapply Mem.perm_store_2; eauto.
    + exists base, len.
      repeat (split; [try assumption | idtac]).
      eapply Mem_range_perm_store; eauto.
  - eapply IHl; eauto.
Qed.

Lemma mem_inv_store_mem_regions_vint:
  forall m m0 chunk l b i vl
    (Hwell_chunk: is_well_chunk chunk)
    (Hmem_inv : inv_memory_regions m0 l)
    (Hstore: Mem.store chunk m0 b (Ptrofs.unsigned i) (vint_to_vint_or_vlong chunk (Vint vl)) = Some m),
      inv_memory_regions m l.
Proof.
  induction l.
  simpl; intros.
  constructor.

  simpl; intros.
  destruct Hmem_inv as (Hmem_inv_mr & Hmem_inv_mrs).
  split.
  -
    unfold inv_memory_region in *.
    destruct Hmem_inv_mr as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstart & Hsize & Hperm & Hrange_perm).
    exists b0.
    repeat (split; [try assumption | idtac]).
    + eapply Mem.store_valid_block_1; eauto.
    + destruct ((b =? b0)%positive) eqn: Hb_eq.
      * rewrite Pos.eqb_eq in Hb_eq.
        subst.
        eapply store_is_byte_block_vint with (v:= Vint vl); eauto.
      * rewrite Pos.eqb_neq in Hb_eq.
        unfold is_byte_block in *.
        erewrite Mem.store_mem_contents; eauto.
        erewrite PMap.gso; eauto.
        intros.
        apply Hbyte.
        eapply Mem.perm_store_2; eauto.
    + exists base, len.
      repeat (split; [try assumption | idtac]).
      eapply Mem_range_perm_store; eauto.
  - eapply IHl; eauto.
Qed.

Lemma mem_inv_store_length:
  forall st1 st2 m chunk b i vl
    (Hmem_inv : Datatypes.length (bpf_mrs st1) = mrs_num st1)
    (Hstore: Mem.store chunk (bpf_m st1) b (Ptrofs.unsigned i) (vlong_to_vint_or_vlong chunk (Vlong vl)) = Some m)
    (Hst2: upd_mem m st1 = st2),
      Datatypes.length (bpf_mrs st2) = mrs_num st2.
Proof.
  intros.
  subst.
  unfold upd_mem, bpf_mrs in *.
  intuition.
Qed.

Lemma mem_inv_store_disjoint:
  forall st1 st2 m chunk b i vl
    (Hmem_inv : disjoint_blocks 0 (bpf_mrs st1))
    (Hstore: Mem.store chunk (bpf_m st1) b (Ptrofs.unsigned i) (vlong_to_vint_or_vlong chunk (Vlong vl)) = Some m)
    (Hst2: upd_mem m st1 = st2),
      disjoint_blocks 0 (bpf_mrs st2).
Proof.
  intros.
  subst.
  unfold upd_mem, bpf_mrs in *.
  intuition.
Qed.

Lemma mem_inv_store_length_vint:
  forall st1 st2 m chunk b i vl
    (Hmem_inv : Datatypes.length (bpf_mrs st1) = mrs_num st1)
    (Hstore: Mem.store chunk (bpf_m st1) b (Ptrofs.unsigned i) (vint_to_vint_or_vlong chunk (Vint vl)) = Some m)
    (Hst2: upd_mem m st1 = st2),
      Datatypes.length (bpf_mrs st2) = mrs_num st2.
Proof.
  intros.
  subst.
  unfold upd_mem, bpf_mrs in *.
  intuition.
Qed.

Lemma mem_inv_store_disjoint_vint:
  forall st1 st2 m chunk b i vl blk
    (Hmem_inv : disjoint_blocks blk (bpf_mrs st1))
    (Hstore: Mem.store chunk (bpf_m st1) b (Ptrofs.unsigned i) (vint_to_vint_or_vlong chunk (Vint vl)) = Some m)
    (Hst2: upd_mem m st1 = st2),
      disjoint_blocks blk (bpf_mrs st2).
Proof.
  intros.
  subst.
  unfold upd_mem, bpf_mrs in *.
  intuition.
Qed.

Lemma store_mem_reg_well_chunk:
  forall st1 chunk addr src
    (Hwell_chunk: is_well_chunk chunk),
    store_mem_reg addr chunk (Vlong src) st1 =
    match
      Mem.storev chunk (bpf_m st1) addr (vlong_to_vint_or_vlong chunk (Vlong src))
    with
    | Some m => Some (upd_mem m st1)
    | None => None
    end.
Proof.
  unfold is_well_chunk, store_mem_reg; intros.
  destruct chunk; try inversion Hwell_chunk.
  all: reflexivity.
Qed.

Lemma mem_inv_store_reg:
  forall st1 st2 chunk addr src
    (Hwell_chunk: is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hstore: store_mem_reg addr chunk (Vlong src) st1 = Some st2),
      memory_inv st2.
Proof.
  intros.
  rewrite store_mem_reg_well_chunk in Hstore; [| assumption].
  unfold vlong_to_vint_or_vlong, Mem.storev in Hstore.
  assert (Hmem_inv' := Hmem_inv).
  unfold memory_inv in Hmem_inv'.
  destruct Hmem_inv' as (Hmem_inv_low & Hmem_inv_length & Hmem_inv_disjoint &_ ).
  unfold memory_inv.

  destruct addr; try inversion Hstore; clear Hstore.
  destruct Mem.store eqn: Hstore; try inversion H0.
  clear H0.

  split.
  unfold upd_mem; simpl; assumption.
  split.
  eapply mem_inv_store_length; eauto.
  split.
  destruct Hmem_inv_disjoint as (start_blk & Hmem_inv_disjoint).
  exists start_blk. unfold upd_mem; simpl. assumption.

  subst.
  clear Hmem_inv_length Hmem_inv_disjoint.
  eapply mem_inv_store_mem_regions_vlong; eauto.
  unfold memory_inv in Hmem_inv.
  intuition.
Qed.

Lemma mem_inv_store_imm_well_chunk:
  forall st1 chunk addr i
    (Hwell_chunk: is_well_chunk chunk),
      store_mem_imm addr chunk (Vint i) st1 =
       match
         match addr with
         | Vptr b ofs =>
             Mem.store chunk (bpf_m st1) b (Ptrofs.unsigned ofs)
               (vint_to_vint_or_vlong chunk (Vint i))
         | _ => None
         end
       with
       | Some m => Some (upd_mem m st1)
       | None => None
       end.
Proof.
  unfold is_well_chunk, store_mem_imm; intros.
  destruct chunk; try inversion Hwell_chunk.
  all: reflexivity.
Qed.

Lemma mem_inv_store_imm:
  forall st1 st2 chunk addr i
    (Hwell_chunk: is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hstore: store_mem_imm addr chunk (Vint i) st1 = Some st2),
      memory_inv st2.
Proof.
  intros.
  rewrite mem_inv_store_imm_well_chunk in Hstore; [| assumption].
  unfold State.vlong_to_vint_or_vlong, Mem.storev in Hstore.
  assert (Hmem_inv' := Hmem_inv).
  unfold memory_inv in Hmem_inv'.
  destruct Hmem_inv' as (Hmem_inv_low & Hmem_inv_length & Hmem_inv_disjoint &_ ).
  unfold memory_inv.

  destruct addr; try inversion Hstore; clear Hstore.
  destruct (Mem.store chunk (bpf_m st1) b (Ptrofs.unsigned i0)) eqn: Hstore; try inversion H0.
  clear H0.

  unfold upd_mem; simpl.
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].

  subst.
  clear Hmem_inv_length Hmem_inv_disjoint.
  eapply mem_inv_store_mem_regions_vint; eauto.
  unfold memory_inv in Hmem_inv.
  intuition.
Qed.


Lemma mem_inv_upd_pc:
  forall st1 st2 p
    (Hmem_inv: memory_inv st1)
    (Hpc: upd_pc p st1 = st2),
      memory_inv st2.
Proof.
  unfold memory_inv.
  intros.
  rewrite <- Hpc.
  simpl; assumption.
Qed.

Lemma mem_inv_upd_pc_incr:
  forall st1 st2
    (Hmem_inv: memory_inv st1)
    (Hpc: upd_pc_incr st1 = st2),
      memory_inv st2.
Proof.
  unfold memory_inv.
  intros.
  rewrite <- Hpc.
  simpl; assumption.
Qed.

Close Scope Z_scope.