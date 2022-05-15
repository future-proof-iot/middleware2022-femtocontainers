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

From compcert Require Import Integers Values Memory AST.
From bpf.comm Require Import State Monad rBPFMonadOp.
From bpf.comm Require Import MemRegion rBPFMemType rBPFAST rBPFValues.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv VerifierInv.

From Coq Require Import ZArith List Lia.
Import ListNotations.

Open Scope Z_scope.

Global Transparent Archi.ptr64.

Ltac unfold_monad :=
  match goal with
  | |- _ =>
    unfold eval_pc, eval_ins, eval_mrs_num, eval_mem, eval_mem_regions, get_addr_ofs, decodeM, upd_reg, upd_flag, eval_src32, eval_src, eval_reg32, upd_pc, upd_pc_incr, eval_reg, eval_ins_len, get_immediate, bindM, returnM
  end.


Ltac destruct_if :=
  repeat match goal with
  | |- context [if ?X then _ else _] =>
    destruct X
  end.

Ltac destruct_ifN Hname :=
  match goal with
  | |- context [if ?X then _ else _] =>
    destruct X eqn: Hname
  end.



Definition is_well_chunk_boolP (chunk: memory_chunk) : bool :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 | Mint64 => true
  | _ => false
  end.

Lemma is_well_chunk_boolM_P:
  forall chunk st,
    is_well_chunk_bool chunk st = Some (is_well_chunk_boolP chunk, st).
Proof.
  unfold is_well_chunk_bool, is_well_chunk_boolP.
  unfold_monad.
  intros.
  destruct chunk; reflexivity.
Qed.

Definition check_mem_aux2P (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): val := (*
  if is_well_chunk_boolP chunk then *)
    let start  := start_addr mr in
    let size   := block_size mr in
    let mr_perm:= block_perm mr in
    let lo_ofs := Val.sub addr start in
    let hi_ofs := Val.add lo_ofs (memory_chunk_to_valu32 chunk) in
      if andb (andb
                  (compu_lt_32 hi_ofs size)
                  (andb (compu_le_32 lo_ofs (memory_chunk_to_valu32_upbound chunk))
                        (comp_eq_32 Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
                (perm_ge mr_perm perm) then
        Val.add (block_ptr mr) lo_ofs (**r Vptr b lo_ofs *)
      else
        Vnullptr. (*
    else
      Vnullptr.*)

Lemma check_mem_aux2M_P:
  forall mr perm addr chunk st,
    check_mem_aux2 mr perm addr chunk st = Some (check_mem_aux2P mr perm addr chunk, st).
Proof.
  unfold check_mem_aux2, check_mem_aux2P.
  unfold get_start_addr, get_block_size, get_sub, get_add, get_block_perm.
  unfold_monad.
  intros.
  destruct_if; reflexivity.
Qed.

Lemma mem_inv_check_mem_aux2P_valid_pointer:
  forall mr p c v st v'
    (Hmem : memory_inv st)
    (Hin_mem_regions: In mr (bpf_mrs st))
    (Hcheck_mem_aux2P: check_mem_aux2P mr p (Vint c) v = v'),
      (exists b ofs, v' = Vptr b ofs /\ (Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs)
    || Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs - 1))%bool = true)
        \/ v' = Vnullptr.
Proof.
  intros.
  unfold memory_inv in Hmem.
  destruct Hmem as (Hlen_low & Hlen & Hdisjoint & Hinv_mem).
  eapply In_inv_memory_regions in Hinv_mem; eauto.
  unfold inv_memory_region in Hinv_mem.
  destruct Hinv_mem as (b & Hptr & Hvalid & His_byte & (start & size & Hstart & Hsize & Hperm & Hrange_perm)).
  unfold Mem.range_perm in Hrange_perm.

  unfold check_mem_aux2P in Hcheck_mem_aux2P.
  unfold is_well_chunk_boolP, compu_lt_32, memory_chunk_to_valu32, compu_le_32, memory_chunk_to_valu32_upbound, comp_eq_32, Vzero, val32_modu, memory_chunk_to_valu32, perm_ge, Vnullptr in Hcheck_mem_aux2P.
  rewrite Hptr, Hstart, Hsize in Hcheck_mem_aux2P.
  revert Hcheck_mem_aux2P.

  assert (Heq: Ptrofs.unsigned (Ptrofs.repr (Int.unsigned (Int.sub c start))) = Int.unsigned (Int.sub c start)). {
    rewrite Ptrofs.unsigned_repr; [reflexivity|].
    change Ptrofs.max_unsigned with Int.max_unsigned.
    apply Int.unsigned_range_2.
  }
  assert (Hle: 0 <= Int.unsigned (Int.sub c start)). {
    assert (Hle1: 0 <= Int.unsigned (Int.sub c start) <= Int.max_unsigned).
    apply Int.unsigned_range_2.
    lia.
  }
  destruct v; simpl.
  all: try (intro Hcheck_mem_aux2P; inversion Hcheck_mem_aux2P; right; reflexivity).
  all: destruct_ifN Hcond; try (unfold Ptrofs.of_int; rewrite Ptrofs.add_zero_l; intro Hcheck_mem_aux2P; try inversion Hcheck_mem_aux2P).
  all: try (intro H; inversion H; right; reflexivity).
  all: left;
    eexists; eexists; split; [ reflexivity |];
    rewrite Bool.orb_true_iff; left;
    rewrite Mem.valid_pointer_nonempty_perm;
    apply Mem.perm_implies with (p1 := MemRegion.block_perm mr); [ | constructor];
    apply Hrange_perm;
    repeat rewrite Bool.andb_true_iff in Hcond.
    all: rewrite Heq; clear Heq;
    split; [ assumption|];
    destruct Hcond as ((Hcond & Hcond0 & _) & _);
    unfold Int.add in Hcond;
    apply Clt_Zlt_iff in Hcond;
    apply Cle_Zle_iff in Hcond0.
Ltac change_const :=
  let I := fresh "I" in
    repeat match goal with
    | H0: Int.unsigned (Int.sub _ _) <= Int.unsigned (Int.repr ?X) |- _ =>
      change (Int.unsigned (Int.repr X)) with X in H0
    | H1: Int.unsigned
            (Int.repr
               (Int.unsigned (Int.sub ?X ?Z) + Int.unsigned (Int.repr ?Y))) <
          Int.unsigned ?W |- _ =>
      change (Int.unsigned (Int.repr Y)) with Y in H1;
      assert (I: Int.unsigned (Int.repr (Int.unsigned (Int.sub X Z) + Y)) = Int.unsigned (Int.sub X Z) + Y); [
      rewrite Int.unsigned_repr; [reflexivity | change Int.max_unsigned with 4294967295; lia] |
      rewrite I in H1; lia
    ]
    end.
    all: change_const.
Qed.

Fixpoint check_mem_auxP (st: state) (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) {struct num}: val :=
  match num with
  | O => Vnullptr
  | S n =>
    let cur_mr    := MyMemRegionsIndexnat mrs n in
    let check_mem := check_mem_aux2P cur_mr perm addr chunk in
      match cmp_ptr32_null (bpf_m st) check_mem with
      | Some res =>
        if res then
          check_mem_auxP st n perm chunk addr mrs
        else
          check_mem
      | None => check_mem
      end
  end.

Lemma check_mem_auxM_P:
  forall n perm chunk addr st
    (Hlt: (n <= mrs_num st)%nat)
    (Hperm: perm_order perm Readable)
    (Hmem_inv : memory_inv st),
    check_mem_aux n perm chunk (Vint addr) (bpf_mrs st) st = Some (check_mem_auxP st n perm chunk (Vint addr) (bpf_mrs st), st).
Proof.
  unfold check_mem_aux, get_mem_region, eval_mrs_regions, check_mem_auxP.
  unfold_monad.
  intros.
  induction n.
  reflexivity.
  assert (Hlt': (n < mrs_num st)%nat) by lia.
  assert (Hlt'': (n <= mrs_num st)%nat) by lia.
  specialize (IHn Hlt''); clear Hlt''.
  rewrite <- Nat.ltb_lt in Hlt'.
  rewrite Hlt'.
  rewrite Nat.ltb_lt in Hlt'.
  set (Hmem_inv' := Hmem_inv).
  unfold memory_inv in Hmem_inv'.
  destruct Hmem_inv' as (_ & Hlen & _ & _).
  rewrite <- Hlen in Hlt'.
  apply nth_error_nth' with (d:= default_memory_region) in Hlt'.
  rewrite Hlt'.
  rewrite check_mem_aux2M_P.
  unfold cmp_ptr32_nullM, State.eval_mem.

  assert (Hcmp: exists res, cmp_ptr32_null (bpf_m st)
      (check_mem_aux2P (MyMemRegionsIndexnat (bpf_mrs st) n) perm 
         (Vint addr) chunk) = Some res). {
    remember (MyMemRegionsIndexnat _ _) as mr.
    unfold MyMemRegionsIndexnat, Memory_regions.index_nat in Heqmr.
    destruct (nth_error _ _) eqn: Hnth_error.
    (**r considering two cases: (MyMemRegionsIndexnat (bpf_mrs st) n) =? In mr (bpf_mr st) \/ default_memory_region *)
    - subst m.
      apply List.nth_error_In in Hnth_error.
      eapply mem_inv_check_mem_aux2P_valid_pointer with (p:= perm) (c:= addr) (v:= chunk) in Hnth_error; eauto.
      destruct Hnth_error as [ Hnth_0 | Hnth_1].
      + destruct Hnth_0 as (b & ofs & Hcheck_mem_aux2P & Hvalid).
        rewrite Hcheck_mem_aux2P.
        unfold cmp_ptr32_null; simpl.
        rewrite Hvalid.
        exists false.
        rewrite Int.eq_true.
        rewrite Bool.andb_true_l.
        reflexivity.
      + unfold cmp_ptr32_null; simpl.
        rewrite Hnth_1.
        unfold Vnullptr; simpl.
        exists true.
        rewrite Int.eq_true.
        reflexivity.
    - subst.
      unfold check_mem_aux2P, default_memory_region.
      unfold start_addr, block_size, block_perm, block_ptr.
      assert (Hnullptr: Vint Int.zero = Vnullptr). {
        unfold Vnullptr; reflexivity.
      }
      rewrite <- Hnullptr; clear Hnullptr.
      assert (Hperm_ge: perm_ge Nonempty perm = false). {
        unfold perm_ge.
        unfold Mem.perm_order_dec.
        destruct perm; try reflexivity.
        inversion Hperm.
      }
      rewrite Hperm_ge; clear Hperm_ge.
      rewrite Bool.andb_false_r.
      destruct_if; try reflexivity.
      all: unfold cmp_ptr32_null; simpl;
      exists true;
      rewrite Int.eq_true;
      reflexivity.
  }

  destruct Hcmp as (res & Hcmp).
  assert (Heq: MyMemRegionsIndexnat (bpf_mrs st) n = nth n (bpf_mrs st) default_memory_region). {
    unfold MyMemRegionsIndexnat, Memory_regions.index_nat.
    rewrite Hlt'.
    reflexivity.
  }
  rewrite <- Heq; clear Heq.
  rewrite Hcmp.
  destruct res; [ | reflexivity].
  unfold cmp_ptr32_nullM, State.eval_mem in IHn.
  rewrite IHn.
  reflexivity.
Qed.

Definition check_memP (perm: permission) (chunk: memory_chunk) (addr: val) (st: State.state): val :=
  let well_chunk := is_well_chunk_boolP chunk in
    if well_chunk then
      let mem_reg_num := eval_mem_num st in
      let mrs         := State.eval_mem_regions st in
      let check_mem  := check_mem_auxP st mem_reg_num perm chunk addr mrs in
        match cmp_ptr32_null (bpf_m st) check_mem with
        | Some res =>
          if res then
            Vnullptr
          else
            check_mem
        | None => Vnullptr
        end
      else
        Vnullptr.

Lemma mem_inv_check_mem_auxP_valid_pointer:
  forall st perm chunk addr v
    (Hperm: perm_order perm Readable)
    (Hmem : memory_inv st)
    (Hcheck_mem_auxP: check_mem_auxP st (mrs_num st) perm chunk (Vint addr) (bpf_mrs st) = v),
      (exists b ofs, v = Vptr b ofs /\ (Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs) || Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs - 1) = true)%bool)
        \/ v = Vnullptr.
Proof.
  intros.

  induction (mrs_num st).
  simpl in Hcheck_mem_auxP.
  subst. right; reflexivity.

  simpl in Hcheck_mem_auxP.

  destruct (cmp_ptr32_null _ _) eqn: Hcmp.
  - destruct b eqn: Hb.
    + apply IHn.
      assumption.
    + unfold cmp_ptr32_null in Hcmp.
      unfold Val.cmpu_bool, Vnullptr in Hcmp; simpl in Hcmp.
      rewrite Hcheck_mem_auxP in Hcmp.
      destruct v; try inversion Hcmp.
      * eapply mem_inv_check_mem_aux2P_valid_pointer in Hcheck_mem_auxP; eauto.
        unfold MyMemRegionsIndexnat, Memory_regions.index_nat in *.
        assert (Hmem' := Hmem).
        destruct Hmem' as (Hlen & Hdisjoint & Hmem').
        destruct nth_error eqn: Hnth; unfold check_mem_aux2P in Hcheck_mem_auxP.
        ** apply nth_error_In in Hnth.
           assumption.
        ** exfalso; unfold default_memory_region, start_addr, block_size, block_perm, block_ptr in Hcheck_mem_auxP.
           assert (Hperm_ge: perm_ge Nonempty perm = false). {
             unfold perm_ge; destruct perm; try constructor.
             inversion Hperm.
           }
           rewrite Hperm_ge in Hcheck_mem_auxP; clear Hperm_ge.
           rewrite Bool.andb_false_r in Hcheck_mem_auxP.
           destruct is_well_chunk_boolP; change Vnullptr with (Vint Int.zero) in *;inversion Hcheck_mem_auxP; subst; rewrite Int.eq_true in H0; inversion H0.
      * left.
        exists b0, i.
        split; [reflexivity | ].
        rewrite Int.eq_true in H0.
        rewrite Bool.andb_true_l in H0.
        destruct (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _)%bool eqn: Hvalid; [reflexivity| inversion H0].
    - unfold cmp_ptr32_null, Val.cmpu_bool, Vnullptr in Hcmp; simpl in Hcmp.
      rewrite Hcheck_mem_auxP in Hcmp.
      assert (Hcheck_mem_auxP' := Hcheck_mem_auxP).
      assert (Hmem' := Hmem).
      destruct Hmem' as (_ & Hlen & Hdisjoint & Hmem').
      unfold MyMemRegionsIndexnat, Memory_regions.index_nat in Hcheck_mem_auxP, Hcheck_mem_auxP'.
      unfold check_mem_aux2P in Hcheck_mem_auxP.
      destruct v; try inversion Hcmp;
      change Vnullptr with (Vint Int.zero) in *. (*
      all: destruct is_well_chunk_boolP; [| inversion Hcheck_mem_auxP]. *)
      all: match goal with
           | H: (if ?X then _ else _) = _ |- _ =>
              destruct X; [| inversion H]
           end.
      5:{ inversion H0. }
      5:{
        destruct nth_error eqn: Hnth; [
        apply nth_error_In in Hnth;
        eapply In_inv_memory_regions in Hmem'; eauto; unfold inv_memory_region in Hmem';
        destruct Hmem' as (b' & Hptr & Hvalid & Hbyte & (start & len & Hstart & Hsize & Hperm_order & Hrange));
        rewrite Hptr, Hstart in Hcheck_mem_auxP |
        unfold default_memory_region, start_addr, block_size, block_perm, block_ptr in Hcheck_mem_auxP;
        change Vnullptr with (Vint Int.zero) in Hcheck_mem_auxP]. 2:{
          assert (Hperm_ge: perm_ge Nonempty perm = false). {
            unfold perm_ge; destruct perm; try constructor.
            inversion Hperm.
          }
          rewrite Hperm_ge in Hcheck_mem_auxP; clear Hperm_ge.
          rewrite Bool.andb_false_r in Hcheck_mem_auxP.
          inversion Hcheck_mem_auxP.
        }
        eapply mem_inv_check_mem_aux2P_valid_pointer in Hcheck_mem_auxP'; eauto.
      }
      all: destruct nth_error eqn: Hnth; [apply nth_error_In in Hnth;
      eapply In_inv_memory_regions in Hmem'; eauto; unfold inv_memory_region in Hmem';
      destruct Hmem' as (b' & Hptr & Hvalid & Hbyte & (start & len & Hstart & Hsize & Hperm_order & Hrange));
      rewrite Hptr, Hstart in Hcheck_mem_auxP; inversion Hcheck_mem_auxP |
      unfold default_memory_region, start_addr, block_size, block_perm, block_ptr in Hcheck_mem_auxP;
      change Vnullptr with (Vint Int.zero) in Hcheck_mem_auxP;
      inversion Hcheck_mem_auxP
      ].
Qed.

Lemma check_memM_P:
  forall perm chunk addr st
    (Hperm: perm_order perm Readable)
    (Hmem_inv : memory_inv st),
    check_mem perm chunk (Vint addr) st = Some (check_memP perm chunk (Vint addr) st, st).
Proof.
  unfold check_mem, eval_mrs_num, eval_mrs_regions, check_memP, cmp_ptr32_nullM, State.eval_mem, State.eval_mem_regions, eval_mem_num.
  unfold_monad.
  intros.
  rewrite is_well_chunk_boolM_P.
  destruct is_well_chunk_boolP; try reflexivity.
  rewrite check_mem_auxM_P; auto.
  remember (check_mem_auxP st (mrs_num st) perm chunk (Vint addr) (bpf_mrs st)) as res.
  symmetry in Heqres.
  eapply mem_inv_check_mem_auxP_valid_pointer in Heqres; eauto.
  destruct Heqres as [(b & ofs & Hptr & Hvalid) | Hnull]; subst; unfold cmp_ptr32_null, Val.cmpu_bool; change Vnullptr with (Vint Int.zero) in *; simpl; rewrite Int.eq_true.
  - rewrite Hvalid; simpl; reflexivity.
  - reflexivity.
Qed.

Lemma well_chunk_iff:
  forall chunk,
    is_well_chunk chunk <-> is_well_chunk_boolP chunk = true.
Proof.
  unfold is_well_chunk, is_well_chunk_boolP.
  intros.
  destruct chunk; split; try constructor; intro H; inversion H.
Qed.


Lemma check_mem_aux2P_spec:
  forall mr chunk st1 p base len b vi ptr
    (Hwell_chunk: is_well_chunk chunk)
    (H0 : check_mem_aux2P mr p (Vint vi) chunk = ptr)
    (Hneq : ptr <> Vnullptr)
    (Hptr : block_ptr mr = Vptr b Ptrofs.zero)
    (Hvalid : Mem.valid_block (bpf_m st1) b)
    (Hbyte : is_byte_block b (bpf_m st1))
    (Hstar : start_addr mr = Vint base)
    (Hsize : block_size mr = Vint len)
    (Hperm : perm_order (block_perm mr) p)
    (Hrange_perm : Mem.range_perm (bpf_m st1) b 0 (Int.unsigned len) Cur (block_perm mr)),
      exists ofs,
        is_well_chunk chunk /\
        ofs = Ptrofs.of_int (Int.sub vi base) /\
        0 <= (Ptrofs.unsigned ofs) + size_chunk chunk < Int.unsigned len /\
        ptr = Vptr b ofs /\
        Mem.valid_access (bpf_m st1) chunk b (Ptrofs.unsigned ofs) (block_perm mr).
Proof.
  unfold check_mem_aux2P.
  intros. (*
  destruct is_well_chunk_boolP eqn: Hwell_chunk; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity]. *)
  rewrite Hptr, Hstar, Hsize in *.
  unfold Val.add, Val.sub in H0.
  rewrite Ptrofs.add_zero_l in H0.
  exists (Ptrofs.of_int (Int.sub vi base)).
  split.
  assumption.

  unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
  val32_modu, Val.add, Val.sub, Vzero in H0.
  match goal with
  | H: (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Hcmp
  end.
  2:{ exfalso; apply Hneq; rewrite H0; reflexivity. }
  
  simpl in H0.
  subst.
  split; [reflexivity | ].

  rewrite Ptrofs.agree32_of_int; [| reflexivity].

  (**r with the fact `is_well_chunk_boolP`, we get the following lemma *)
  assert (Heq_well_chunk: well_chunk_Z chunk = size_chunk chunk). {
    unfold is_well_chunk_boolP in Hwell_chunk.
    destruct chunk; try inversion Hwell_chunk.
    all: unfold well_chunk_Z, size_chunk; reflexivity.
  }
  rewrite Heq_well_chunk in *; clear Heq_well_chunk.

  apply andb_prop in Hcmp.
  destruct Hcmp as (Hcmp & Hperm_ge).
  apply andb_prop in Hcmp.
  destruct Hcmp as (Hlow & Hcmp).
  apply andb_prop in Hcmp.
  destruct Hcmp as (Hhigh & Hmod).

  (**r Hlow is for _ <= _ < _ and Hhigh is for valid_access *)
  apply (hi_ofs_max_unsigned (Int.sub vi base) chunk) in Hhigh.
  apply Clt_implies_Zlt_add in Hlow as Hlow'; [| assumption].
  split; [ assumption | ].

  split.
  reflexivity.

  unfold Mem.valid_access.
  split.
  eapply range_perm_included; eauto.
  apply Int_unsigned_ge_0.
  apply Int_unsigned_ofs_size_chunk_ge_0.
  intuition.

  destruct Val.modu eqn: Hmod1; [| inversion Hmod].
  destruct v; try inversion Hmod.
  unfold Val.modu in Hmod1.
  destruct Int.eq eqn: Hmod2; [inversion Hmod1|].
  eapply modu_zero_is_aligned; eauto.
  inversion Hmod1.
  rewrite <- H1 in H0.
  assumption.
Qed.

Lemma mem_inv_check_mem_valid_pointer:
  forall st perm chunk addr v
    (Hperm: perm_order perm Readable)
    (Hmem : memory_inv st)
    (Hcheck_memP: check_memP perm chunk (Vint addr) st = v),
      (exists b ofs, v = Vptr b ofs /\ (Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs) || Mem.valid_pointer (bpf_m st) b (Ptrofs.unsigned ofs - 1) = true)%bool)
        \/ v = Vnullptr.
Proof.
  unfold check_memP; intros.
  unfold is_well_chunk_boolP in Hcheck_memP.
  unfold cmp_ptr32_null in Hcheck_memP.
  unfold Val.cmpu_bool in Hcheck_memP.
  unfold State.eval_mem_regions in Hcheck_memP.
  remember (check_mem_auxP st (eval_mem_num st) perm chunk (Vint addr) (bpf_mrs st)) as res.
  symmetry in Heqres.
  eapply mem_inv_check_mem_auxP_valid_pointer with (perm:= perm) (addr := addr) in Heqres; eauto.
  change Vnullptr with (Vint (Int.zero)) in *.
  simpl in *.
  destruct chunk; try (right; symmetry; assumption).
  all: destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; rewrite Hptr in *.
  all: rewrite Int.eq_true in Hcheck_memP; try rewrite Bool.andb_true_l in Hcheck_memP.
  all: try (right; symmetry; assumption).
  all: left; exists b, ofs.
  all: rewrite Hvalid in Hcheck_memP.
  all: auto.
Qed.