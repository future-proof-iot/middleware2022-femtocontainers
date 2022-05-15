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
From bpf.comm Require Import State MemRegion Regs Flag List64.
From compcert Require Import Coqlib Integers Values AST Clight Memory Memtype.

From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic.
From Coq Require Import ZArith.
Open Scope Z_scope.

(**r


Definition mem_region_def: Ctypes.composite_definition := 
  Ctypes.Composite mem_region_id Ctypes.Struct [
    (start_addr_id, C_U32);
    (size_id, C_U32);
    (perm_id, C_U32);
    (block_ptr_id, C_U32)
  ] Ctypes.noattr.

*)

Global Transparent Archi.ptr64.

Definition match_region_at_ofs (mr:memory_region) (state_blk mrs_blk ins_blk: block) (ofs : ptrofs) (m: mem)  : Prop :=
  (exists vl,  Mem.loadv AST.Mint32 m (Vptr mrs_blk ofs) = Some (Vint vl) /\ (start_addr mr) = Vint vl)    /\ (**r start_addr mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr mrs_blk (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint vl) /\ (block_size mr) = Vint vl) /\ (**r block_size mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr mrs_blk (Ptrofs.add ofs (Ptrofs.repr 8))) = Some (Vint vl) /\ correct_perm (block_perm mr)  vl) /\ (**r block_perm mr = Vint vl*)
    (exists b, Mem.loadv AST.Mptr  m (Vptr mrs_blk (Ptrofs.add ofs (Ptrofs.repr 12))) = Some (Vptr b Ptrofs.zero) /\ (block_ptr mr) = Vptr b Ptrofs.zero /\ (Mem.valid_block m b /\ b <> state_blk /\ b <> mrs_blk /\ b <> ins_blk)).


(*Definition size_of_region  :=  16. (* 4 * 32 bits *)*)
(*
Fixpoint match_list_region (m:mem) (bl_regions: block) (ofs:ptrofs) (l:list memory_region) :=
  match l with
  | nil => True
  | mr :: l' => match_region_at_ofs  mr bl_regions ofs m /\
                  match_list_region  m bl_regions (Ptrofs.add ofs (Ptrofs.repr 16)) l'
  end. *)

(*
Fixpoint match_list_region (m:mem) (b: block) (ofs: nat) (l:list memory_region) :=
  match l with
  | nil => True
  | mr :: l' => match_region_at_ofs mr b (Ptrofs.repr (16 * Z.of_nat ofs)) m /\ match_list_region m b (ofs+1) l'
  end. *)

Definition match_list_region (m:mem) (state_blk mrs_blk ins_blk: block) (l:list memory_region) :=
  forall i, (0 <= i < List.length l)%nat -> match_region_at_ofs (List.nth i l default_memory_region) state_blk mrs_blk ins_blk (Ptrofs.repr (16 * Z.of_nat i)) m.

Definition match_regions (state_blk mrs_blk ins_blk: block) (st: State.state) (m:mem) :=
  List.length (bpf_mrs st) = (mrs_num st) /\ (**r the number of bpf_mrs is exactly the mrs_num *)
  Z.of_nat (List.length (bpf_mrs st)) * 16 <= Ptrofs.max_unsigned /\ (**r there is not overflow *)
  match_list_region m state_blk mrs_blk ins_blk (bpf_mrs st).


Lemma match_regions_in:
  forall l mr m state_blk mrs_blk ins_blk
    (Hnth_error : In mr l)
    (Hmatch : match_list_region m state_blk mrs_blk ins_blk l),
      exists n, match_region_at_ofs mr state_blk mrs_blk ins_blk (Ptrofs.repr (16 * Z.of_nat n)) m.
Proof.
  unfold match_list_region.
  intros.
  apply In_nth_error in Hnth_error.
  destruct Hnth_error as (n & Hnth_error).
  apply nth_error_some_length in Hnth_error as Hlen.
  specialize (Hmatch n Hlen).
  destruct Hlen as ( _ & Hlen).
  apply nth_error_nth' with (d:= default_memory_region) in Hlen.
  rewrite Hlen in Hnth_error.
  inversion Hnth_error.
  subst.
  exists n; assumption.
Qed.

(*
Fixpoint match_list_ins (m:mem) (b: block) (ofs:ptrofs) (l: MyListType) :=
  match l with
  | nil => True
  | hd :: tl => Mem.loadv AST.Mint64 m (Vptr b ofs) = Some (Vlong hd) /\
                  match_list_ins m b (Ptrofs.add ofs (Ptrofs.repr 8)) tl
  end. *)

Definition match_list_ins (m:mem) (b: block) (l: list int64) :=
  forall i, (0 <= i < List.length l)%nat ->
    Mem.loadv AST.Mint64 m  (Vptr b (Ptrofs.repr (8 * (Z.of_nat i)))) = Some (Vlong (List.nth i l Int64.zero)) (*/\
    0 <= (Int64.unsigned (Int64.shru (Int64.and (List.nth i l Int64.zero) (Int64.repr 4095)) (Int64.repr 8))) <= 10 /\ (**r dst \in [0,10] *)
    0 <= (Int64.unsigned (Int64.shru (Int64.and (List.nth i l Int64.zero) (Int64.repr 65535)) (Int64.repr 12))) <= 10 (**r src \in [0,10] *) *).

Definition match_ins (ins_blk: block) (st: State.state) (m:mem) :=
  List.length (ins st) = (ins_len st) /\
  Z.of_nat (List.length (ins st)) * 8 <= Ptrofs.max_unsigned /\
  match_list_ins m ins_blk (ins st).


Class special_blocks : Type :=
  { st_blk : block;
    mrs_blk  : block;
    ins_blk  : block }.

Section S.

  Context {Blocks : special_blocks}.

  Definition match_registers  (rmap:regmap) (bl_reg:block) (ofs : ptrofs) (m : mem) : Prop:=
    forall (r:reg),
    exists vl, Mem.loadv Mint64 m (Vptr bl_reg (Ptrofs.add ofs (Ptrofs.repr (8 * (id_of_reg r))))) = Some (Vlong vl) /\ (**r it should be `(eval_regmap r rmap)`*)
            Vlong vl = eval_regmap r rmap.
           (*Val.inject inject_id (eval_regmap r rmap) (Vlong vl) . (**r each register is Vlong *)*)


  (*Definition size_of_regs := 88. (**r 11 * 8: we have 11 regs R0 - R10 *)*)
  Definition size_of_state (st: State.state) := 100 + 16 * (Z.of_nat (mrs_num st)) + 8 *(Z.of_nat (ins_len st)).

(**r
Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [
    (pc_id, C_U32);
    (flag_id, C_S32);
    (regmaps_id, C_regmap);;
    (mem_num_id, C_U32)
    (mem_regs_id, mem_region_type)
  ] Ctypes.noattr.

*)

  Record match_state  (st: State.state) (m: mem) : Prop :=
    {
      munchange: Mem.unchanged_on (fun b _ => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) (bpf_m st) m; (**r (bpf_m st) = m - {state_blk, mrs_blk, ins_blk} *)
      mpc      : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 0)) = Some (Vint  (pc_loc st));
      mflags   : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 4)) = Some (Vint  (int_of_flag (flag st)));
      mregs    : match_registers (regs_st st) st_blk (Ptrofs.repr 8) m;
      mins_len : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 96)) = Some (Vint  (Int.repr (Z.of_nat (ins_len st)))) /\ Z.of_nat (ins_len st) >= 1;
      mins     : Mem.loadv AST.Mptr m (Vptr st_blk (Ptrofs.repr 100)) = Some (Vptr ins_blk (Ptrofs.repr 0)) /\ match_ins ins_blk st m;
      mmrs_num : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 104)) = Some (Vint  (Int.repr (Z.of_nat (mrs_num st)))) /\
                 (Z.of_nat(mrs_num st)) >= 1; (**r at least we have the memory region that corresponds to the input paramters of the interpreter *)
      mem_regs : Mem.loadv AST.Mptr m (Vptr st_blk (Ptrofs.repr 108)) = Some (Vptr mrs_blk (Ptrofs.repr 0)) /\ match_regions st_blk mrs_blk ins_blk st m;
      mperm    : Mem.range_perm m st_blk 0 (size_of_state st) Cur Freeable /\
                 Mem.range_perm m mrs_blk   0 (Z.of_nat (mrs_num st)) Cur Freeable /\
                 Mem.range_perm m ins_blk   0 (Z.of_nat (ins_len st)) Cur Readable; (**r we also need to say `mrs/ins_blk` *)
      minvalid : (~Mem.valid_block (bpf_m st) st_blk /\
                  ~Mem.valid_block (bpf_m st) mrs_blk /\
                  ~Mem.valid_block (bpf_m st) ins_blk) /\
                 (mrs_blk <> st_blk /\ mrs_blk <> ins_blk /\ ins_blk <> st_blk) /\
                 (forall b, b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk ->
                  Mem.valid_block m b -> Mem.valid_block (bpf_m st) b);
    }.

End S.

(* Permission Lemmas: deriving from riot-rbpf/MemInv.v *)
Lemma range_perm_included:
  forall m b p lo hi ofs_lo ofs_hi, 
    lo <= ofs_lo -> ofs_lo < ofs_hi -> ofs_hi <= hi ->  (**r `<` -> `<=` *)
    Mem.range_perm m b lo hi Cur p ->
      Mem.range_perm m b ofs_lo ofs_hi Cur p.
Proof.
  intros.
  apply (Mem.range_perm_implies _ _ _ _ _ p _); [idtac | constructor].
  unfold Mem.range_perm in *; intros.
  apply H2.
  lia.
Qed.

(** Permission Lemmas: upd_pc *)
Lemma upd_pc_write_access:
  forall m0 {bl:special_blocks} st
    (Hst: match_state  st m0),
    Mem.valid_access m0 Mint32 st_blk 0 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mem_regs0 mperm0; simpl in mem_regs0.
  unfold match_regions, size_of_state in *.
  destruct mperm0 as (mperm0 & _ & _).
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].

  unfold size_chunk, align_chunk.
  split.
  - simpl; apply (range_perm_included _ _ Writable _ _ 0 4) in mperm0; [assumption | lia | lia | idtac].
    assert (H: 0<= Z.of_nat (State.mrs_num st)). { apply Nat2Z.is_nonneg. }
    lia.
  - apply Z.divide_0_r.
Qed.

Lemma upd_pc_store:
  forall m0 {S: special_blocks} pc st
    (Hst: match_state  st m0),
    exists m1,
    Mem.store AST.Mint32 m0 st_blk 0 (Vint pc) = Some m1.
Proof.
  intros.
  apply upd_pc_write_access  in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint pc)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_flags *)
Lemma upd_flags_write_access:
  forall m0 {S:special_blocks} st
    (Hst: match_state  st m0),
    Mem.valid_access m0 Mint32 st_blk 4 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  unfold size_of_state in *.
  destruct mperm0 as (mperm0 & _ & _).
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].

  unfold size_chunk, align_chunk.
  split.
  - simpl.
    apply (range_perm_included _ _ Writable _ _ 4 8) in mperm0; [assumption | lia | lia | lia].
  - apply Z.divide_refl.
Qed.

Lemma upd_flags_store:
  forall m0 {S: special_blocks} st v
    (Hst: match_state  st m0),
    exists m1,
    Mem.store AST.Mint32 m0 st_blk 4 (Vint v) = Some m1.
Proof.
  intros.
  apply (upd_flags_write_access _ _ ) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_regs *)
Lemma upd_regs_write_access:
  forall m0 {S: special_blocks} st r
    (Hst: match_state  st m0),
    Mem.valid_access m0 Mint64 st_blk (8 + (8 * (id_of_reg r))) Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  unfold size_of_state in *.
  destruct mperm0 as (mperm0 & _ & _).
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].
  assert (H: 0<= Z.of_nat (State.mrs_num st)). { apply Nat2Z.is_nonneg. }
  apply (range_perm_included _ _ Writable _ _ 0 100) in mperm0; [idtac | lia | lia | lia].

  unfold id_of_reg.
  unfold size_chunk, align_chunk.
  split.
  - apply (range_perm_included _ _ Writable _ _ (8 + (8 * (id_of_reg r))) (8 + (8 * (id_of_reg r +1)))) in mperm0;
  destruct r; simpl in *; try lia; try assumption.
  - assert (Heq: forall x, 8 + 8 * x = 8 * (1 + x)). {
      intros.
      rewrite Zred_factor2.
      reflexivity.
    }
    rewrite Heq.
    apply Z.divide_factor_l.
Qed.

Lemma upd_regs_store:
  forall m0 {S: special_blocks} st r v
    (Hst: match_state  st m0),
    exists m1,
    Mem.store AST.Mint64 m0 st_blk (8 + (8 * (id_of_reg r))) (Vlong v) = Some m1.
Proof.
  intros.
  apply upd_regs_write_access with (r:=r) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vlong v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_mem_regions *)

(** TODO: nothing to do because we never update memory_regions, it should be done before running the interpter *)

Definition match_region (st_blk mrs_blk ins_blk : block) (mr: memory_region) (v: val) (st: State.state) (m:Memory.Mem.mem) :=
  exists o, v = Vptr mrs_blk o /\
              match_region_at_ofs mr st_blk mrs_blk ins_blk o m.

(*
Definition match_region_list (st_blk mrs_blk ins_blk: block) (mrl: list memory_region) (v: val) (st: State.state) (m:Memory.Mem.mem) :=
  v = Vptr mrs_blk Ptrofs.zero /\
  mrl = (bpf_mrs st) /\
  List.length mrl = (mrs_num st) /\ (**r those two are from the match_state relation *)
  match_list_region m st_blk mrs_blk ins_blk mrl. *)

Lemma same_memory_match_region :
  forall st_blk mrs_blk ins_blk st st' m m' mr v
         (UMOD : unmodifies_effect ModNothing m m' st st'),
    match_region st_blk mrs_blk ins_blk mr v st m ->
    match_region st_blk mrs_blk ins_blk mr v st' m'.
Proof.
  intros.
  unfold match_region in *.
  destruct H as (o & E & MR).
  exists o.
  split; auto.
  unfold match_region_at_ofs in *.
  unfold unmodifies_effect in UMOD.
  destruct UMOD; subst.
  repeat rewrite <- UMOD by (simpl ; tauto).
  intuition.
Qed.

(**r a set of lemmas say upd_reg/flag/pc... don't change the memory/regs/flag/pc of rbpf *)

Lemma upd_reg_same_mem:
  forall st0 r vl,
    bpf_m st0 = bpf_m (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_pc:
  forall st0 r vl,
    pc_loc st0 = pc_loc (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_flag:
  forall st0 r vl,
    flag st0 = flag (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_mrs:
  forall st0 r vl,
    bpf_mrs st0 = bpf_mrs (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_mrs_num:
  forall st0 r vl,
    State.mrs_num st0 = State.mrs_num (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_ins:
  forall st0 r vl,
    ins st0 = ins (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_ins_len:
  forall st0 r vl,
    ins_len st0 = ins_len (State.upd_reg r vl st0).
Proof.
  unfold State.upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mem:
  forall st0 pc,
    bpf_m st0 = bpf_m (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_regs:
  forall st0 pc,
    regs_st st0 = regs_st (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_flag:
  forall st0 pc,
    flag st0 = flag (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mrs:
  forall st0 pc,
    bpf_mrs st0 = bpf_mrs (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mrs_num:
  forall st0 pc,
    State.mrs_num st0 = State.mrs_num (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_ins:
  forall st0 pc,
    ins st0 = ins (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_ins_len:
  forall st0 pc,
    ins_len st0 = ins_len (State.upd_pc pc st0).
Proof.
  unfold State.upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_mem:
  forall st0,
    bpf_m st0 = bpf_m (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_regs:
  forall st0,
    regs_st st0 = regs_st (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_flag:
  forall st0,
    flag st0 = flag (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_mrs:
  forall st0,
    bpf_mrs st0 = bpf_mrs (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_mrs_num:
  forall st0,
    State.mrs_num st0 = State.mrs_num (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_ins:
  forall st0,
    ins st0 = ins (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_incr_same_ins_len:
  forall st0,
    ins_len st0 = ins_len (State.upd_pc_incr st0).
Proof.
  unfold State.upd_pc_incr.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mem:
  forall st0 f,
    bpf_m st0 = bpf_m (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_regs:
  forall st0 f,
    regs_st st0 = regs_st (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_pc:
  forall st0 f,
    pc_loc st0 = pc_loc (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mrs:
  forall st0 f,
    bpf_mrs st0 = bpf_mrs (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mrs_num:
  forall st0 f,
    State.mrs_num st0 = State.mrs_num (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_ins:
  forall st0 f,
    ins st0 = ins (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_ins_len:
  forall st0 f,
    ins_len st0 = ins_len (State.upd_flag f st0).
Proof.
  unfold State.upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_unchanged_on:
  forall st m0 m1 {S:special_blocks} chunk ofs vl
  (Hst    : match_state  st m0)
  (Hstore : Mem.store chunk m0 st_blk ofs vl = Some m1),
    Mem.unchanged_on (fun b _ => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1.
Proof.
  intros.
  destruct Hst. (*
  destruct minj0.
  clear - mi_inj mi_freeblocks minvalid0 munchange0 mByte0 Hstore. *)
  eapply Mem.store_unchanged_on.
  rewrite Hstore.
  reflexivity.
  intros.
  intro.
  destruct H0 as (H0 & _).
  apply H0; reflexivity.
Qed.

Lemma upd_preserves_match_list_ins:
  forall l chunk m0 m1 st_blk ins_blk ofs0 vl
  (Hstore : Mem.store chunk m0 st_blk ofs0 vl = Some m1)
  (mem_regs : match_list_ins m0 ins_blk l)
  (Hneq_blk : st_blk <> ins_blk),
    match_list_ins m1 ins_blk l.
Proof.
  intro l.
  induction l.
  unfold match_list_ins in *.
  intros.
  simpl in H.
  lia.

  intros; simpl in *.
  unfold match_list_ins in *.
  intros.
  specialize (mem_regs0 i H).
  unfold Mem.loadv in *. (*
  destruct mem_regs0 as (mem_regs0 & Hdst & Hsrc). *)
  rewrite <- mem_regs0.
  eapply Mem.load_store_other; eauto.
   (*
  split.
  eapply Mem.load_store_other; eauto.
  split; assumption. *)
Qed.

Lemma upd_preserves_match_list_region:
  forall l chunk m0 m1 st_blk mrs_blk ins_blk b ofs0 vl
  (Hstore : Mem.store chunk m0 b ofs0 vl = Some m1)
  (mem_regs : match_list_region m0 st_blk mrs_blk ins_blk l)
  (Hneq_blk : b <> mrs_blk),
    match_list_region m1 st_blk mrs_blk ins_blk l.
Proof.
  intro l.
  induction l;
  unfold match_list_region in *.
  intros; simpl in *.
  lia.

  intros.
  unfold match_region_at_ofs in *.
  specialize (mem_regs0 i H).
  destruct mem_regs0 as  ((vl0 & Hload0 & Heq0) & (vl1 & Hload1 & Heq1) & (vl2 & Hload2 & Heq2) & (blk3 & Hload3 & Heq_ptr)).

  split.
  exists vl0; rewrite <- Hload0; split; [
  eapply Mem.load_store_other; eauto | assumption].

  split.
  exists vl1; rewrite <- Hload1; split; [
  eapply Mem.load_store_other; eauto | assumption].

  split.
  exists vl2; rewrite <- Hload2; split; [
  eapply Mem.load_store_other; eauto | assumption].

  exists blk3; rewrite <- Hload3; split; [
  eapply Mem.load_store_other; eauto | ].
  intuition.
  eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma upd_reg_preserves_match_state:
  forall st0 st1 m0 m1 {S:special_blocks} r vl
  (Hst    : match_state  st0 m0)
  (Hst1   : State.upd_reg r (Vlong vl) st0 = st1)
  (Hstore : Mem.store AST.Mint64 m0 st_blk (8 + 8 * id_of_reg r) (Vlong vl) = Some m1),
    match_state  st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  destruct Hst'.
  split; unfold Mem.loadv in *.
  -
    rewrite <- (upd_reg_same_mem _ r (Vlong vl)).
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro.
      destruct H0 as (H0 & _).
      apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    rewrite <- (upd_reg_same_pc _ r (Vlong vl)).
    rewrite <- mpc0.
    eapply Mem.load_store_other; eauto.
    right; left.
    unfold id_of_reg; simpl.
    fold Ptrofs.zero.
    rewrite Ptrofs.unsigned_zero.
    destruct r; try lia.
  - rewrite <- (upd_reg_same_flag _ r (Vlong vl)).
    rewrite <- mflags0.
    eapply Mem.load_store_other; eauto.
    right; left.
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    unfold id_of_reg; simpl; destruct r; try lia.
  - unfold match_registers in *.
    intros.
    specialize (mregs0 r0).
    destruct mregs0 as (vl0 & mregs0 & mregs1).
    unfold Mem.loadv, Ptrofs.add in *.

    rewrite Hreg_eq in *.
    destruct (reg_eq r0 r).
    + (**r case: r0 = r *)
      subst.
      exists vl.
      split.
      assert (Hload_result: Val.load_result Mint64 (Vlong vl) = (Vlong vl)). {
        reflexivity.
      }
      rewrite <- Hload_result.
      eapply Mem.load_store_same; eauto.
      unfold State.upd_reg; simpl.
      rewrite eval_upd_regmap_same.
      reflexivity.
    +
      exists vl0.
      unfold State.upd_reg, regs_st.
      
      rewrite eval_upd_regmap_other.
      split.
      2:{
        rewrite mregs1.
        reflexivity.
      }
      rewrite <- mregs0.
      eapply Mem.load_store_other; eauto.
      right.
      2:{ assumption. }
      destruct r0, r; simpl; [try (exfalso; apply n; reflexivity) || (try left; lia) || (try right; lia) ..].
  - simpl.
    destruct mins_len0 as (mins_len0 & mins_len1).
    split; [| assumption].

    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite <- mins_len0.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold id_of_reg, size_chunk; destruct r; lia.
  - (**r match_ins *)
    unfold match_ins.
    unfold match_ins in mins0.
    destruct mins0 as (Hload & mins_len & mins_max & mins0).
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.

    split; [assumption | ].
    split; [assumption | ].
    assert (Hins_eq : ins (State.upd_reg r (Vlong vl) st0) = ins st0). {
      unfold State.upd_reg.
      simpl.
      reflexivity.
    }
    rewrite Hins_eq; clear Hins_eq.
    destruct minvalid0 as (_ & minvalid0 & _).
    eapply upd_preserves_match_list_ins; eauto. intuition.
  - rewrite <- (upd_reg_same_mrs_num _ r (Vlong vl)).
    destruct mmrs_num0 as (Hload & Hge).
    split; [| assumption].
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold size_chunk.
    assert (Hle_104: 8 + 8 * id_of_reg r + 8 <= 104). { unfold id_of_reg; destruct r; lia. }
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    assumption.
  - unfold match_regions in *.
    destruct mem_regs0 as (Hload & mrs_len & mrs_max & mem_regs0).
    rewrite <- (upd_reg_same_mrs _ r (Vlong vl)).

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.

    split; [assumption | ].
    split; [assumption | ].
    destruct minvalid0 as (_ & minvalid0 & _).
    eapply upd_preserves_match_list_region; eauto. intuition.

  - clear - mperm0 Hstore.
    unfold Mem.range_perm in *.
    destruct mperm0 as (mperm0 & mperm1 & mperm2).
    split; intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply mperm0.
    unfold size_of_state in *.
    rewrite <- upd_reg_same_mrs_num in *.
    assumption.
    split; intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply mperm1.
    unfold size_of_state in *.
    rewrite <- upd_reg_same_mrs_num in *.
    assumption.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply mperm2.
    unfold size_of_state in *.
    rewrite <- upd_reg_same_ins_len in *.
    assumption.
  - rewrite <- upd_reg_same_mem.
    intuition.
    apply H14; auto.
    eapply Mem.store_valid_block_2; eauto.
Qed.


Lemma upd_pc_preserves_match_state:
  forall st0 st1 m0 m1 {S:special_blocks} pc
  (Hst    : match_state  st0 m0)
  (Hst1   : State.upd_pc pc st0 = st1)
  (Hstore : Mem.store AST.Mint32 m0 st_blk 0 (Vint pc) = Some m1),
    match_state  st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  split.
  -
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_mem.
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro.
      destruct H0 as(H0 & _).
      apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    destruct Hst' as (_ , Hpc, _, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    fold Ptrofs.zero in *.
    rewrite Ptrofs.unsigned_zero in *.
    apply Mem.load_store_same in Hstore.
    rewrite Hstore.
    unfold Val.load_result.
    reflexivity.
  -
    destruct Hst' as (_ , _, Hflag, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_flag.
    rewrite <- Hflag.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    reflexivity.
  -
    destruct Hst' as (_ , _, _, Hregs, _, _, _, _, _, _).
    rewrite <- upd_pc_same_regs.
    unfold match_registers in *.
    intros.
    specialize (Hregs r).
    destruct Hregs as (vl & Hload & Hvl_eq).
    exists vl.
    split; [| assumption].
    rewrite <- Hload.
    unfold Mem.loadv.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    unfold Ptrofs.add in *.
    unfold size_chunk.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_id_of_reg in *.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg; destruct r; lia.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n with (n:= 8 * id_of_reg r) in *; try (simpl; lia).
    all: unfold id_of_reg; destruct r; lia.
  - 
    destruct Hst' as (_ , _, _, _, (Hins_len & Hge), _, _, _, _, _).
    rewrite <- upd_pc_same_ins_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, Hins, _, _, _, (_ & Hneq_blk & _)).
    unfold match_ins in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_pc_same_ins.
    rewrite <- upd_pc_same_ins_len.
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_ins; eauto. intuition.
  - 
    destruct Hst' as (_ , _, _, _, _, _, (Hmrs_len & Hge), _, _, _).
    rewrite <- upd_pc_same_mrs_num.
    split; [| assumption].
    rewrite <- Hmrs_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, _, _, Hmrs, _, (_ & Hneq_blk & _)).
    unfold match_regions in *.
    rewrite <- upd_pc_same_mrs.
    rewrite <- upd_pc_same_mrs_num.
    destruct Hmrs as (Hload & Hmrs_len & Hmrs_ge & Hmrs).


    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto. intuition.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, Hperm, _).
    unfold size_of_state in *.
    rewrite <- upd_pc_same_mrs_num.
    unfold Mem.range_perm in *.
    destruct Hperm as (Hperm0 & Hperm1 & Hperm2).
    split; intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm0.
    assumption.
    split; intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm1.
    assumption.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm2.
    assumption.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, Hvalid).
    rewrite <- upd_pc_same_mem.
    intuition.
    apply H3; auto.
    eapply Mem.store_valid_block_2; eauto.
Qed.

Lemma upd_flag_preserves_match_state:
  forall st0 st1 m0 m1 {S: special_blocks} flag
  (Hst    : match_state  st0 m0)
  (Hst1   : State.upd_flag flag st0 = st1)
  (Hstore : Mem.store AST.Mint32 m0 st_blk 4 (Vint (int_of_flag flag)) = Some m1),
    match_state  st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  split.
  -
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_mem.
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro H0; destruct H0 as (H0 & _); apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    destruct Hst' as (_ , Hpc, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_pc.
    rewrite <- Hpc.
    eapply Mem.load_store_other.
    apply Hstore.
    right; left.
    fold Ptrofs.zero; rewrite Ptrofs.unsigned_zero.
    reflexivity.
  -
    destruct Hst' as (_ , _, Hflag, _, _, _, _, _, _, _).

    unfold Mem.loadv in *.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    apply Mem.load_store_same in Hstore.
    rewrite Hstore.
    unfold Val.load_result.
    reflexivity.
  -
    destruct Hst' as (_ , _, _, Hregs, _, _, _, _, _, _).
    rewrite <- upd_flag_same_regs.
    unfold match_registers in *.
    intros.
    specialize (Hregs r).
    destruct Hregs as (vl & Hload & Hvl_eq).
    exists vl.
    split; [| assumption].
    rewrite <- Hload.
    unfold Mem.loadv.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    unfold Ptrofs.add in *.
    unfold size_chunk.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    4:
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    4:
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    all: unfold id_of_reg; destruct r; lia.
  -
    destruct Hst' as (_ , _, _, _, (Hins_len & Hge), _, _, _, _, _).
    rewrite <- upd_flag_same_ins_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, Hins, _, _, _, (_ & Hneq_blk & _)).
    unfold match_ins in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_flag_same_ins.
    rewrite <- upd_flag_same_ins_len.

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_ins; eauto. intuition.
  -
    destruct Hst' as (_ , _, _, _, _, _, (Hmrs_len & Hge), _, _, _).
    rewrite <- upd_flag_same_mrs_num.
    split; [| assumption].
    rewrite <- Hmrs_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, _, _, Hmrs, _, (_ & Hneq_blk & _)).
    unfold match_regions in *.
    rewrite <- upd_flag_same_mrs.
    rewrite <- upd_flag_same_mrs_num.
    destruct Hmrs as (Hload & Hmrs_len & Hmrs_ge & Hmrs).

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto. intuition.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, Hperm, _).
    unfold size_of_state in *.
    rewrite <- upd_flag_same_mrs_num.
    unfold Mem.range_perm in *.
    destruct Hperm as (Hperm0 & Hperm1 & Hperm2).
    split; intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm0.
    assumption.
    split; intros.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm1.
    assumption.
    eapply Mem.perm_store_1.
    apply Hstore.
    apply Hperm2.
    assumption.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, Hvalid).
    rewrite <- upd_flag_same_mem.
    intuition.
    apply H3; auto.
    eapply Mem.store_valid_block_2; eauto.
Qed.

Lemma match_state_implies_valid_pointer:
  forall  {S:special_blocks} st m b ofs
    (Hmatch : match_state  st m)
    (Hvalid : Mem.valid_pointer (bpf_m st) b ofs = true),
      Mem.valid_pointer m b ofs = true.
Proof.
  intros.
  rewrite Mem.valid_pointer_nonempty_perm in *.
  destruct Hmatch.
  eapply Mem.perm_unchanged_on; eauto.
  simpl.
  apply Mem.perm_valid_block in Hvalid.
  clear - minvalid0 Hvalid.
  destruct minvalid0 as ((Hv0 & Hv1 & Hv2) & H).
  repeat split.
  all: eapply Mem.valid_not_valid_diff; eauto.
Qed.

Lemma match_state_implies_loadv_equal:
  forall {S: special_blocks} st m chunk b ofs v
    (Hmatch : match_state  st m)
    (Hload: Mem.load chunk (bpf_m st) b ofs = Some v),
      Mem.load chunk m b ofs = Some v.
Proof.
  intros.
  set (Hmatch' := Hmatch).
  destruct Hmatch' as (Hunchanged, _, _, _, _, _, _, _, _, Hinvalid).
  rewrite <- Hload.
  destruct Hinvalid as (Hinvalid & _ & Hvalid_block).
  apply Mem.load_valid_access in Hload.
  assert (Hload' : Mem.valid_access (bpf_m st) chunk b ofs Nonempty). {
    eapply Mem.valid_access_implies; eauto.
    constructor.
  }
  eapply Mem.valid_access_valid_block in Hload'; eauto.
  eapply Mem.load_unchanged_on_1; eauto.
  simpl; intros.
  intuition congruence.
Qed.

Lemma store_perm_iff:
  forall chunk m1 m2 b ofs addr b0 ofs0 k p
  (Hstore : Mem.store chunk m1 b ofs addr = Some m2),
      Mem.perm m1 b0 ofs0 k p <-> Mem.perm m2 b0 ofs0 k p.
Proof.
  intros.
  split; intro.
  - eapply Mem.perm_store_1 with (k:=k) (p:=p) in Hstore; eauto.
  - eapply Mem.perm_store_2 with (k:=k) (p:=p) in Hstore; eauto.
Qed.

Lemma store_match_state_same:
  forall st1 m m1 m2 chunk b ofs addr
    (Hstore : Mem.store chunk (bpf_m st1) b ofs addr = Some m)
    (Hstore_m2 : Mem.store chunk m1 b ofs addr = Some m2)
    (Hunchanged_on_contents : Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1)) =
                        Maps.ZMap.get ofs
                          (Maps.PMap.get b (Mem.mem_contents (bpf_m st1)))),
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m2)) =
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)).
Proof.
  intros.
  apply Mem.store_mem_contents in Hstore as Hcontents0; auto.
  apply Mem.store_mem_contents in Hstore_m2 as Hcontents1; auto.
  rewrite Hcontents0, Hcontents1.
  repeat rewrite Maps.PMap.gss.
  clear - Hunchanged_on_contents.
  generalize (encode_val chunk addr).
  intros.
  destruct l.
  - simpl.
    assumption.
  - simpl.
    rewrite Mem.setN_other; [|intros; lia].
    rewrite Mem.setN_other; [|intros; lia].
    repeat rewrite Maps.ZMap.gss.
    reflexivity.
Qed.

(**r the proof code comes from MisakaCenter (QQ), thx *)
Lemma mem_get_in:
  forall l (n:nat) q c,
  lt n (List.length l) ->
    Maps.ZMap.get (q + (Z.of_nat n)) (Mem.setN l q c) = (nth_default Memdata.Undef l n).
Proof.
  induction l; simpl in *; intros.
  lia.
  induction n; simpl.
  - unfold nth_default; simpl.
    rewrite Mem.setN_outside; try lia.
    rewrite Z.add_0_r.
    rewrite Maps.ZMap.gss; auto.
  - assert (Heq: nth_default Memdata.Undef (a::l) (S n) = nth_default Memdata.Undef l n) by auto.
    rewrite Heq; clear Heq.
    rewrite <- IHl with (q := q+1) (c:=Maps.ZMap.set q a c).
    assert (Heq: q + Z.pos (Pos.of_succ_nat n) = q + 1 + Z.of_nat n) by lia.
    rewrite Heq; clear Heq.
    reflexivity.
    lia.
Qed.

Lemma store_match_state_same_other:
  forall st1 m m1 m2 chunk b ofs ofs0 addr
    (Hstore : Mem.store chunk (bpf_m st1) b ofs addr = Some m)
    (Hstore_m2 : Mem.store chunk m1 b ofs addr = Some m2)
    (Hother: ofs < ofs0 < ofs + size_chunk chunk)
    (Hunchanged_on_contents : Maps.ZMap.get ofs0 (Maps.PMap.get b (Mem.mem_contents m1)) =
                        Maps.ZMap.get ofs0
                          (Maps.PMap.get b (Mem.mem_contents (bpf_m st1)))),
      Maps.ZMap.get ofs0 (Maps.PMap.get b (Mem.mem_contents m2)) =
      Maps.ZMap.get ofs0 (Maps.PMap.get b (Mem.mem_contents m)).
Proof.
  intros.
  apply Mem.store_mem_contents in Hstore as Hcontents0; auto.
  apply Mem.store_mem_contents in Hstore_m2 as Hcontents1; auto.
  rewrite Hcontents0, Hcontents1.
  repeat rewrite Maps.PMap.gss.

  assert (Hlen: List.length (encode_val chunk addr) = size_chunk_nat chunk) by apply encode_val_length.
  revert Hlen.
  generalize (encode_val chunk addr).
  unfold size_chunk_nat.
  intros.
  assert (Hofs0_eq: exists n, 0 < Z.of_nat n < size_chunk chunk /\ ofs0 = ofs+ Z.of_nat n). {
    clear - Hother.
    assert (Heq: Z.of_nat (Z.to_nat (ofs0 - ofs)) = ofs0 - ofs). {
      rewrite Z2Nat.id.
      reflexivity.
      lia.
    }
    exists (Z.to_nat(ofs0 - ofs)).
    lia.
  }
  destruct Hofs0_eq as (z & Hz_range & Hofs0_eq); subst.
  repeat rewrite mem_get_in.
  reflexivity.
  lia.
  lia.
Qed.

Lemma store_match_state_other:
  forall st1 m m1 m2 chunk b ofs addr
    (Hstore : Mem.store chunk (bpf_m st1) b ofs addr = Some m)
    (Hstore_m2 : Mem.store chunk m1 b ofs addr = Some m2),
    forall b0 ofs0
    (Hother: b0 <> b \/ ofs0 < ofs \/ ofs + size_chunk chunk <= ofs0)
    (Hunchanged_on_contents :
      Maps.ZMap.get ofs0 (Maps.PMap.get b0 (Mem.mem_contents m1)) =
      Maps.ZMap.get ofs0 (Maps.PMap.get b0 (Mem.mem_contents (bpf_m st1)))),
      Maps.ZMap.get ofs0 (Maps.PMap.get b0 (Mem.mem_contents m2)) =
      Maps.ZMap.get ofs0 (Maps.PMap.get b0 (Mem.mem_contents m)).
Proof.
  intros.
  apply Mem.store_mem_contents in Hstore as Hcontents0; auto.
  apply Mem.store_mem_contents in Hstore_m2 as Hcontents1; auto.
  rewrite Hcontents0, Hcontents1.
  destruct (b0 =? b)%positive eqn: Hblk_eq; [rewrite Pos.eqb_eq in Hblk_eq | rewrite Pos.eqb_neq in Hblk_eq].
  - subst.
    repeat rewrite Maps.PMap.gss.
    destruct Hother as [Hfalse | Hother]; [intuition|].
    repeat rewrite Mem.setN_outside.
    + assumption.
    + rewrite Memdata.encode_val_length.
      unfold size_chunk_nat, size_chunk.
      unfold size_chunk in Hother.
      destruct Hother as [Hle | Hge].
      * left.
        lia.
      * right.
        destruct chunk; lia.
    + rewrite Memdata.encode_val_length.
      unfold size_chunk_nat, size_chunk.
      unfold size_chunk in Hother.
      destruct Hother as [Hle | Hge].
      * left.
        lia.
      * right.
        destruct chunk; lia.
  - repeat (rewrite Maps.PMap.gso; [| lia]).
    assumption.
Qed.

Lemma store_range_perm:
  forall chunk m1 m2 b0 b1 ofs addr low high k p
    (Hblk_neq: b0 <> b1)
    (Hstore : Mem.store chunk m1 b0 ofs addr = Some m2)
    (Hrange_perm : Mem.range_perm m1 b1 low high k p),
      Mem.range_perm m2 b1 low high k p.
Proof.
  intros.
  unfold Mem.range_perm in *.
  intros.
  specialize (Hrange_perm ofs0 H).
  eapply Mem.perm_store_1; eauto.
Qed.

Lemma store_reg_preserive_match_state:
  forall {S:special_blocks} st1 st2 m1 chunk b ofs addr m
    (Hst: match_state  st1 m1)
    (Hstore: Mem.store chunk (bpf_m st1) b ofs addr = Some m)
    (Hupd_st: upd_mem m st1 = st2),
      exists m2,
        Mem.store chunk m1 b ofs addr = Some m2 /\
        match_state  st2 m2.
Proof.
  intros.
  assert (Hvalid_blk': Mem.valid_block (bpf_m st1) b). {
    destruct Hst as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    apply Mem.store_valid_access_3 in Hstore.
    assert (Hstore' : Mem.valid_access (bpf_m st1) chunk b ofs Nonempty). {
      eapply Mem.valid_access_implies; eauto.
      constructor.
    }
    eapply Mem.valid_access_valid_block in Hstore'; eauto.
  }
  assert (Hvalid_blk: Mem.valid_block m1 b). {
    destruct Hst as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    eapply Mem.valid_block_unchanged_on; eauto.
  }

  assert (Hinvalid: b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk). {
    destruct Hst as (_, _, _, _, _, _, _, _, _, Hinvalid).
    destruct Hinvalid as ((Hinvalid0 & Hinvalid1 & Hinvalid2) & _ & _).
    split.
    intro; subst.
    apply Hinvalid0; assumption.
    split; intro; subst.
    apply Hinvalid1; assumption.
    apply Hinvalid2; assumption.
  }

  assert (Hvalid_access: Mem.valid_access m1 chunk b ofs Writable). {
    destruct Hst.
    destruct minvalid0 as ( _ & _ & Hvalid).
    specialize (Hvalid b Hinvalid Hvalid_blk).
    clear - munchange0 Hvalid Hvalid_blk Hinvalid Hstore.
    destruct munchange0.

    eapply Mem.store_valid_access_3 in Hstore as Hvalid_acc; eauto.
    eapply Mem.valid_access_store with (v:= addr) in Hvalid_acc as Hres; eauto.

    unfold Mem.valid_access in *.
    destruct Hvalid_acc as (Hvalid_acc & Haligh).
    split; [| assumption].
    unfold Mem.range_perm in *.
    intros.
    specialize (Hvalid_acc ofs0 H).
    specialize (unchanged_on_perm b ofs0 Cur Writable Hinvalid Hvalid).
    apply unchanged_on_perm; assumption.
  }
  eapply Mem.valid_access_store with (v:= addr) in Hvalid_access; eauto.
  destruct Hvalid_access as (m2 & Hstore_m2).
  exists m2.
  split; [assumption |].

  subst.
  set (Hst' := Hst).
  split.
  - (**r Mem.unchanged_on *)
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _).
    destruct Hunchanged_on.
    unfold upd_mem; simpl.
    split.
    + eapply Mem.nextblock_store in Hstore_m2; auto.
      rewrite Hstore_m2.
      eapply Mem.nextblock_store in Hstore; auto.
      rewrite Hstore.
      assumption.
    + intros.
      eapply Mem.store_valid_block_2 in Hstore as Hvalid_block; eauto.
      specialize (unchanged_on_perm b0 ofs0 k p H Hvalid_block).
      eapply store_perm_iff with (b0:=b0) (ofs0:=ofs0) (k:=k) (p:=p) in Hstore as Hperm_1; eauto.
      eapply store_perm_iff with (b0:=b0) (ofs0:=ofs0) (k:=k) (p:=p) in Hstore_m2 as Hperm_2; eauto.
      intuition.
    + intros.
      eapply Mem.perm_store_2 in Hstore as Hperm; eauto.
      specialize (unchanged_on_contents b0 ofs0 H Hperm).
      clear unchanged_on_nextblock unchanged_on_perm H0 Hperm.

      destruct (b0 =? b)%positive eqn: Hblk_eq; [rewrite Pos.eqb_eq in Hblk_eq | rewrite Pos.eqb_neq in Hblk_eq].
      * (**r b0 = b *)
        subst.
        destruct (ofs0 =? ofs)%Z eqn: Hofs_eq; [rewrite Z.eqb_eq in Hofs_eq | rewrite Z.eqb_neq in Hofs_eq].
        ** (**r ofs0 = ofs *)
          subst.
          eapply store_match_state_same; eauto.
        ** (**r ofs0 <> ofs *)
          rewrite Z.lt_gt_cases in Hofs_eq.
          destruct Hofs_eq as [Hofs_le | Hofs_ge].
          { (**r ofs0 < ofs*)
            eapply store_match_state_other; eauto.
          }
          { (**r ofs < ofs0 *)
            destruct (ofs + size_chunk chunk <=? ofs0)%Z eqn: Hge; [rewrite Z.leb_le in Hge | rewrite Z.leb_gt in Hge].
            { (**r ofs + size_chunk chunk <= ofs0 *)
              eapply store_match_state_other; eauto.
            }
            { (**r ofs < ofs0 < ofs + size_chunk chunk *)
              eapply store_match_state_same_other; eauto.
            }
          }
      * (**r b0 <> b *)
        eapply store_match_state_other; eauto.
  - (**r pc *)
    destruct Hst' as (_, Hpc, _, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl.
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r flag *)
    destruct Hst' as (_, _, Hflag, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl.
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r registers *)
    destruct Hst' as (_, _, _, Hreg, _, _, _, _, _, _).
    unfold match_registers in *.
    intros.
    specialize (Hreg r).
    destruct Hreg as (vl & Hload & Hvl_eq).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl regs_st.
    exists vl.
    split; [| assumption].
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r ins_len *)
    destruct Hst' as (_, _, _, _, Hins_len, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl.
    destruct Hins_len as (Hload & Hge).
    split; [| assumption].
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r ins *)
    destruct Hst' as (_, _, _, _, _, Hins, _, _, _, _).
    unfold Mem.loadv in *.
    unfold match_ins in *.
    destruct Hins as (Hload & Hlen & Hmax & Hmatch).
    unfold upd_mem; simpl.
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_ins; eauto.
    intuition.
  - (**r mrs_num *)
    destruct Hst' as (_, _, _, _, _, _, Hmrs_num, _, _, _).
    unfold Mem.loadv in *.
    destruct Hmrs_num as (Hload & Hother).
    unfold upd_mem; simpl.
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    assumption.
  - (**r mrs_block *)
    destruct Hst' as (_, _, _, _, _, _, _, Hmrs_block, _, _).
    unfold Mem.loadv in *.
    unfold match_regions in *.
    unfold upd_mem; simpl.
    destruct Hmrs_block as (Hload & Hlen & Hmax & Hmatch).
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto.
    intuition.
  - (**r range_perm *)
    destruct Hst' as (_, _, _, _, _, _, _, _, Hrange_perm, _).
    unfold size_of_state in *.
    unfold upd_mem.
    simpl mrs_num.
    simpl ins_len.
    destruct Hrange_perm as (Hrange_perm_st & Hrange_perm_mrs & Hrange_perm_ins).
    split; [eapply store_range_perm; eauto; intuition |].
    split; eapply store_range_perm; eauto; intuition.
  - (**r valid_block *)
    destruct Hst' as (_, _, _, _, _, _, _, _, _, Hvalid_block).
    unfold upd_mem; simpl.
    destruct Hvalid_block as (Hinvalid_blk & Hneq_blk & Hvalid).
    destruct Hinvalid_blk as (Hinvalid_blk0 & Hinvalid_blk1 & Hinvalid_blk2).
    split.
    split.
    intro H; apply Hinvalid_blk0; eapply Mem.store_valid_block_2; eauto.
    split.
    intro H; apply Hinvalid_blk1; eapply Mem.store_valid_block_2; eauto.
    intro H; apply Hinvalid_blk2; eapply Mem.store_valid_block_2; eauto.
    split; [assumption | ].
    intros.
    specialize (Hvalid b0 H).
    eapply Mem.store_valid_block_2 in Hstore_m2; eauto.
    specialize (Hvalid Hstore_m2).
    eapply Mem.store_valid_block_1 in Hstore; eauto.
Qed.

Close Scope Z_scope.

#[global] Notation dcons := (DList.DCons (F:= fun x => x -> Inv State.state)).
