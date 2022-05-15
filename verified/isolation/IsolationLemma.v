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
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv VerifierInv CheckMem StateInv.

From Coq Require Import ZArith List Lia.
Import ListNotations.

Open Scope Z_scope.


Lemma step_preserving_inv_alu:
  forall st st1 st2 a b r s t
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem : step_alu_binary_operation a b r s st1 = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.
  unfold step_alu_binary_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r) in Hreg as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  destruct a; rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
  all: destruct s.
  all: try (apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
    destruct Heval_reg as (src0 & Heval_reg);
    rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem).

  all: destruct b; inversion Hsem; clear Hsem;
      [ split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]] |

        split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]);
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto] |
          split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]] |
        split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0;
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto] |
          split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]] |
        split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0;
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto] |
          split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]] |
        split; (destruct negb eqn: Hnegb; [rewrite Bool.negb_true_iff in Hnegb; rewrite Hnegb in H0; simpl in H0; inversion H0 | rewrite Bool.negb_false_iff in Hnegb; inversion H0]);
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto] |
          split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]] |
        split; [eapply reg_inv_upd_reg; eauto |
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto]] |
        split; destruct Int.ltu eqn: Hltu; simpl in H0; inversion H0; clear H0;
        [ eapply reg_inv_upd_reg; eauto |
          eapply reg_inv_upd_flag; eauto|
          split; [eapply mem_inv_upd_reg; eauto | eapply state_include_upd_reg; eauto] |
          split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]]].
Qed.

Lemma step_preserving_inv_branch:
  forall st st1 st2 c r s o t
    (Hreg : register_inv st1)
    (Hmem : memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem : match step_branch_cond c r s st1 with
       | Some (x', st') =>
           (if x'
            then
             fun st : state =>
             if
              Int.cmpu Cle (Int.add (State.eval_pc st1) o)
                (Int.sub (Int.repr (Z.of_nat (ins_len st))) (Int.repr 2))
             then Some (tt, State.upd_pc (Int.add (State.eval_pc st1) o) st)
             else None
            else fun st : state => Some (tt, st)) st'
       | None => None
       end = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.
  unfold step_branch_cond; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r) in Hreg as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
  destruct s.
  - (**r inl r *)
    apply reg_inv_eval_reg with (r := r0) in Hreg as Heval_reg;
    destruct Heval_reg as (src0 & Heval_reg).
    rewrite Heval_reg in Hsem; clear Heval_reg; simpl in Hsem.
    destruct (match c with
         | Eq => Int64.eq src src0
         | Gt Ctypes.Signed => Int64.lt src0 src
         | Gt Ctypes.Unsigned => Int64.ltu src0 src
         | Ge Ctypes.Signed => negb (Int64.lt src src0)
         | Ge Ctypes.Unsigned => negb (Int64.ltu src src0)
         | Lt Ctypes.Signed => Int64.lt src src0
         | Lt Ctypes.Unsigned => Int64.ltu src src0
         | Le Ctypes.Signed => negb (Int64.lt src0 src)
         | Le Ctypes.Unsigned => negb (Int64.ltu src0 src)
         | SEt => negb (Int64.eq (Int64.and src src0) Int64.zero)
         | Ne => negb (Int64.eq src src0)
         end); inversion Hsem; clear Hsem.
    + match goal with
      | H : (if ?X then _ else _) = _ |- _ =>
        destruct X; inversion H
      end.
      split; [eapply reg_inv_upd_pc; eauto |
        split; [eapply mem_inv_upd_pc; eauto | eapply state_include_upd_pc; eauto]].
    + subst; intuition.
  - (**r inr i *)
    destruct (match c with
         | Eq => Int64.eq src (Int64.repr (Int.signed i))
         | Gt Ctypes.Signed => Int64.lt (Int64.repr (Int.signed i)) src
         | Gt Ctypes.Unsigned => Int64.ltu (Int64.repr (Int.signed i)) src
         | Ge Ctypes.Signed => negb (Int64.lt src (Int64.repr (Int.signed i)))
         | Ge Ctypes.Unsigned =>
             negb (Int64.ltu src (Int64.repr (Int.signed i)))
         | Lt Ctypes.Signed => Int64.lt src (Int64.repr (Int.signed i))
         | Lt Ctypes.Unsigned => Int64.ltu src (Int64.repr (Int.signed i))
         | Le Ctypes.Signed => negb (Int64.lt (Int64.repr (Int.signed i)) src)
         | Le Ctypes.Unsigned =>
             negb (Int64.ltu (Int64.repr (Int.signed i)) src)
         | SEt =>
             negb
               (Int64.eq (Int64.and src (Int64.repr (Int.signed i)))
                  Int64.zero)
         | Ne => negb (Int64.eq src (Int64.repr (Int.signed i)))
         end); inversion Hsem; clear Hsem.
    + match goal with
      | H : (if ?X then _ else _) = _ |- _ =>
        destruct X; inversion H
      end.
      split; [eapply reg_inv_upd_pc; eauto |
        split; [eapply mem_inv_upd_pc; eauto | eapply state_include_upd_pc; eauto]].
    + subst; intuition.
Qed.

Lemma step_preserving_inv_ld:
  forall st st1 st2 m r r0 o t
    (Hreg_inv : register_inv st1)
    (Hmem_inv : memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem : step_load_x_operation m r r0 o st1 = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.
  unfold step_load_x_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r0) in Hreg_inv as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  (**r addr = Vint ... *)
  rewrite Heval_reg in Hsem.
  unfold val_intuoflongu, Val.longofint, sint32_to_vint, Val.addl in Hsem.
  remember (Int.repr (Int64.unsigned (Int64.add src (Int64.repr (Int.signed o))))) as addr.

  assert (Hperm: perm_order Readable Readable). { constructor. }

  assert (Hcheck_mem: exists ret, check_mem Memtype.Readable m (Vint addr) st1 = Some (ret, st1)). {
    rewrite check_memM_P; auto.
    eexists; reflexivity.
  }
  destruct Hcheck_mem as (ret & Hcheck_mem); rewrite Hcheck_mem in Hsem; clear Hcheck_mem.
  unfold cmp_ptr32_nullM in Hsem.
  destruct cmp_ptr32_null; inversion Hsem; clear Hsem.
  destruct b; inversion H0; subst.
  - split; [eapply reg_inv_upd_flag; eauto |
      split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
  - unfold load_mem in H1.
    destruct State.load_mem in H1; inversion H1.
    destruct v in H1; inversion H1.
    split; [eapply reg_inv_upd_reg; eauto |
      split; [eapply mem_inv_upd_reg; eauto |eapply state_include_upd_reg; eauto]].
Qed.

Lemma step_preserving_inv_st:
  forall st st1 st2 m r s o t
    (Hreg_inv : register_inv st1)
    (Hmem_inv : memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem : step_store_operation m r s o st1 = Some (t, st2)),
      register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.
  unfold step_store_operation; unfold_monad; intros.
  apply reg_inv_eval_reg with (r := r) in Hreg_inv as Heval_reg;
  destruct Heval_reg as (src & Heval_reg).
  (**r addr = Vint ... *)
  rewrite Heval_reg in Hsem.
  unfold val_intuoflongu, Val.longofint, sint32_to_vint, Val.addl in Hsem.
  remember (Int.repr (Int64.unsigned (Int64.add src (Int64.repr (Int.signed o))))) as addr.

  assert (Hperm: perm_order Writable Readable). { constructor. }
  assert (Hcheck_mem: exists ret, check_mem Writable m (Vint addr) st1 = Some (ret, st1)). {
    rewrite check_memM_P; auto.
    eexists; reflexivity.
  }

  destruct s; destruct Hcheck_mem as (ret & Hcheck_mem); rewrite Hcheck_mem in Hsem;
  unfold cmp_ptr32_nullM in Hsem;
  (destruct cmp_ptr32_null eqn: Hptr; [| inversion Hsem]).
  - (**r inl r *)
    destruct b; inversion Hsem; subst.
    + split; [eapply reg_inv_upd_flag; eauto |
        split; [eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
    + clear H0.
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.cmp_ptr32_null in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; try constructor.
      }
      apply reg_inv_eval_reg with (r := r0) in Hreg_inv as Heval_reg0;
      destruct Heval_reg0 as (src0 & Heval_reg0).
      rewrite Heval_reg0 in Hsem; clear Heval_reg0; simpl in Hsem.
      unfold store_mem_reg in Hsem.
      destruct State.store_mem_reg eqn: Hstore; [| inversion Hsem].
      inversion Hsem; subst.
      split; [eapply reg_inv_store_reg; eauto |
        split; [eapply mem_inv_store_reg; eauto | eapply state_include_store_reg; eauto]].

  - (**r inr i *)
    destruct b; inversion Hsem; subst.
    + split; [eapply reg_inv_upd_flag; eauto |
        split; [ eapply mem_inv_upd_flag; eauto | eapply state_include_upd_flag; eauto]].
    +
      (**r from the fact Hptr and Hcheck_mem, we know Hwell_chunk *)
      assert (Hwell_chunk: is_well_chunk m). {
        unfold rBPFValues.cmp_ptr32_null in Hptr.
        unfold check_mem, bindM, returnM in Hcheck_mem.
        destruct m; simpl in Hcheck_mem; inversion Hcheck_mem; unfold Vnullptr in *; subst; simpl in Hptr;
        try (rewrite Int.eq_true in Hptr; inversion Hptr).
        all: unfold is_well_chunk; constructor.
      }
      unfold rBPFValues.sint32_to_vint, store_mem_imm in Hsem.
      destruct State.store_mem_imm eqn: Hstore; [| inversion Hsem].
      inversion Hsem; subst.
      split; [eapply reg_inv_store_imm; eauto |
        split; [eapply mem_inv_store_imm; eauto | eapply state_include_store_imm; eauto]].
Qed.

Lemma check_mem_load:
  forall chunk st1 vi pt
    (Hwell_chunk : is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hcheck_mem: check_mem Readable chunk (Vint vi) st1 = Some (pt, st1))
    (Hneq: pt <> Vnullptr),
    exists res,
      (Memory.Mem.loadv chunk (bpf_m st1) pt = Some res)/\
      is_vlong_or_vint res.
Proof.
  intros.
  rewrite check_memM_P in Hcheck_mem; auto.
  2:{ constructor. }
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  change Vnullptr with (Vint Int.zero) in *.
  destruct cmp_ptr32_null eqn: Hcmp; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
  destruct b; [rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity | ].

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  { (**r  mrs_num st1 = 0 *)
    simpl in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    rewrite H0 in Hneq.
    exfalso; apply Hneq; reflexivity.
  }

  simpl in *.
  destruct (cmp_ptr32_null _ (check_mem_aux2P _ _ _ _))eqn: Hcmp1;
  [| rewrite Hcmp1 in Hcmp ]; inversion Hcmp.
  destruct b.
  {
    apply IHn; auto.
  }
  rewrite H0.

  unfold MyMemRegionsIndexnat, Memory_regions.index_nat in H0.
  destruct nth_error eqn: Hnth.
  2:{ (**r it is impossible to return Vptr b ofs in H0 *)
    unfold default_memory_region, check_mem_aux2P in H0.
    unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
  val32_modu, Val.add, Val.sub, Vzero, start_addr, block_size, block_perm, block_ptr in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X eqn: Heq; [ | rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity]
    end.
    assert (Hperm_ge: perm_ge Nonempty Readable = false). {
      unfold perm_ge; constructor.
    }
    rewrite Hperm_ge in Heq; clear Hperm_ge.
    rewrite Bool.andb_false_r in Heq.
    inversion Heq.
  }

  apply nth_error_In in Hnth.
  destruct Hmem_inv as (_ & Hlen & Hdisjoint & Hmem_inv).
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) (mr := m) in Hmem_inv; [| intuition].
  assert (Hmem_inv' := Hmem_inv).
  unfold inv_memory_region in Hmem_inv'.

  destruct Hmem_inv' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstar & Hsize & Hperm & Hrange_perm).
  eapply check_mem_aux2P_spec in H0; eauto.
  destruct H0 as (ofs & Hwell_chunk' & Hofs & Hofs_range & Hptr_eq & Hvalid_access).

  subst pt.
  apply Mem.valid_access_implies with (p2:= Readable) in Hvalid_access; [| assumption].
  apply Mem.valid_access_load in Hvalid_access.
  destruct Hvalid_access as (v & Hload).
  exists v.
  unfold Mem.loadv.
  split; [assumption | ].

  assert (Hofs_range_c: 0 <= Ptrofs.unsigned ofs /\ Ptrofs.unsigned ofs + size_chunk chunk < Int.unsigned len). {
      split.
      apply ptrofs_unsigned_ge_0.
      destruct Hofs_range as [Ha Hb]; assumption.
    }

  eapply load_some_well_chunk_vlong_or_vint; eauto.
  apply well_chunk_iff; assumption.
Qed.

Definition vlong_or_vint_to_vint_or_vlong (chunk: memory_chunk) (v: val): val :=
  match v with
  | Vlong n => vlong_to_vint_or_vlong chunk v
  | Vint  n => vint_to_vint_or_vlong chunk v
  | _       => Vundef
  end.

Lemma check_mem_store:
  forall chunk st1 vi v pt
    (Hwell_chunk : is_well_chunk chunk)
    (Hmem_inv: memory_inv st1)
    (Hvlong_vint: is_vlong_or_vint v)
    (Hcheck_mem: check_mem Writable chunk (Vint vi) st1 = Some (pt, st1))
    (Hneq: pt <> Vnullptr),
    exists m,
      (Mem.storev chunk (bpf_m st1) pt (vlong_or_vint_to_vint_or_vlong chunk v) = Some m)/\
      memory_inv (upd_mem m st1).
Proof.
  intros.
  rewrite check_memM_P in Hcheck_mem; auto.
  2:{ constructor. }
  inversion Hcheck_mem; clear Hcheck_mem.

  unfold check_memP in *.
  rewrite well_chunk_iff in Hwell_chunk.
  rewrite Hwell_chunk in *.
  change Vnullptr with (Vint Int.zero) in *.
  destruct cmp_ptr32_null eqn: Hcmp; [| rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity].
  destruct b; [rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity | ].

  unfold eval_mem_num, State.eval_mem_regions in *.

  induction (mrs_num st1).
  { (**r  mrs_num st1 = 0 *)
    simpl in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    rewrite H0 in Hneq.
    exfalso; apply Hneq; reflexivity.
  }

  simpl in *.
  destruct (cmp_ptr32_null _ (check_mem_aux2P _ _ _ _))eqn: Hcmp1;
  [| rewrite Hcmp1 in Hcmp ]; inversion Hcmp.
  destruct b.
  {
    apply IHn; auto.
  }
  rewrite H0.

  unfold MyMemRegionsIndexnat, Memory_regions.index_nat in H0.
  destruct nth_error eqn: Hnth.
  2:{ (**r it is impossible to return Vptr b ofs in H0 *)
    unfold default_memory_region, check_mem_aux2P in H0.
    unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
  val32_modu, Val.add, Val.sub, Vzero, start_addr, block_size, block_perm, block_ptr in H0.
    change Vnullptr with (Vint Int.zero) in H0.
    match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X eqn: Heq; [ | rewrite H0 in Hneq; exfalso; apply Hneq; reflexivity]
    end.
    assert (Hperm_ge: perm_ge Nonempty Writable = false). {
      unfold perm_ge; constructor.
    }
    rewrite Hperm_ge in Heq; clear Hperm_ge.
    rewrite Bool.andb_false_r in Heq.
    inversion Heq.
  }

  apply nth_error_In in Hnth.
  assert (Hmem_inv' := Hmem_inv).
  destruct Hmem_inv' as (_ & Hlen & Hdisjoint & Hmem_inv').
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) (mr := m) in Hmem_inv'; [| intuition].


  destruct Hmem_inv' as (b0 & Hptr & Hvalid & Hbyte & base & len & Hstart & Hsize & Hperm & Hrange_perm).

  assert (Hperm_w: perm_order (block_perm m) Writable). {
    unfold check_mem_aux2P in H0.
    rewrite Hptr, Hstart, Hsize in H0.
    unfold compu_lt_32, compu_le_32, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound, comp_eq_32,
    val32_modu, Val.add, Val.sub, Vzero in H0.
    change Vnullptr with (Vint Int.zero) in H0.

    clear Hcmp1.
    match goal with
    | H: (if ?X then _ else _) = _ |- _ =>
      destruct X eqn: Hcmp1
    end.
    2:{ exfalso; apply Hneq; rewrite H0; reflexivity. }
    clear - Hcmp1.
    rewrite Bool.andb_true_iff in Hcmp1.
    destruct Hcmp1 as (_ & Hperm).
    unfold perm_ge in Hperm.
    destruct Mem.perm_order_dec; [ assumption | inversion Hperm].
  }

  eapply check_mem_aux2P_spec in H0; eauto.
  destruct H0 as (ofs & Hwell_chunk' & Hofs & Hofs_range & Hptr_eq & Hvalid_access).
  subst pt.

  apply Mem.valid_access_implies with (p2:= Writable) in Hvalid_access; [| assumption].
  eapply Mem.valid_access_store in Hvalid_access; eauto.
  destruct Hvalid_access as (m2 & Hstore).
  exists m2.
  split; [ apply Hstore | ].

  (**r prove the memory_inv *)
  unfold is_vlong_or_vint in Hvlong_vint.
  destruct v; inversion Hvlong_vint.

  - apply mem_inv_store_imm with (st1 := st1) (st2:= upd_mem m2 st1) (addr:= Vptr b0 ofs) (i:= i) in Hwell_chunk'; auto.
    rewrite mem_inv_store_imm_well_chunk; [| rewrite well_chunk_iff; assumption].
    unfold vint_to_vint_or_vlong.

    unfold vlong_or_vint_to_vint_or_vlong, vint_to_vint_or_vlong in Hstore.
    rewrite Hstore.
    reflexivity.
  - unfold vlong_or_vint_to_vint_or_vlong, vlong_to_vint_or_vlong in Hstore.
    apply mem_inv_store_reg with (st1 := st1) (st2:= upd_mem m2 st1) (addr:= Vptr b0 ofs) (src:= i) in Hwell_chunk'; auto.
  unfold State.store_mem_reg, vlong_to_vint_or_vlong.
    destruct chunk; try inversion Hwell_chunk'; simpl.
    all: try (rewrite Hstore; reflexivity).
  - apply well_chunk_iff; assumption.
Qed.
