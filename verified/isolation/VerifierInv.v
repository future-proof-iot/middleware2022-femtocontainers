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

From compcert Require Import Integers Values.
From bpf.comm Require Import Regs BinrBPF State LemmaNat.
From bpf.model Require Import Semantics.
From bpf.isolation Require Import AlignChunk CommonISOLib VerifierOpcode.
From bpf.verifier.comm Require Import state.
From Coq Require Import ZArith Lia List.
Import ListNotations.


Ltac destruct_if_zeqb Hname :=
  match goal with
  | |- context [(if ?X then _ else _) = Some _] =>
    destruct X eqn: Hname;
    [ eexists; rewrite Z.eqb_eq in Hname; rewrite Hname;
  reflexivity |
      rewrite Z.eqb_neq in Hname]
  end.


Open Scope nat_scope.
(**r CertrBPF needs the following two properties guaranteed by an assumed rbpf verifier, we will implement a verified verifier later~

\begin{enumerate}
    \item dst \& src registers are in [0, 10].
    \item all jump operations are always within in bound.
    tbc...
    \item when ins.opcode = div, ins.src != 0
    \item when ins.opcode = shift (lsh/rsh/arsh), $0 \leq ins.src \leq 32/64$
    \item etc... (more ambitious: {\color{red} check\_mem = true?}  ...)  
\end{enumerate}

 *)

Definition is_well_dst (i: int64) : bool := Int.cmpu Cle (Int.repr (get_dst i)) (Int.repr 10).

Definition is_well_src (i: int64) : bool := Int.cmpu Cle (Int.repr (get_src i)) (Int.repr 10).

Definition is_well_jump (pc len: nat) (ofs: int) : bool :=
  Int.cmpu Cle (Int.add (Int.repr (Z.of_nat pc)) ofs) (Int.sub (Int.repr (Z.of_nat len)) (Int.repr 2%Z)).
(*
Definition is_well_jump (pc len: nat) (ofs: int) : bool :=
  Int.cmpu Clt (Int.add (Int.repr (Z.of_nat pc)) ofs) (Int.repr (Z.of_nat len)). *)

Definition is_not_div_by_zero (i: int64) : bool :=
  Int.cmp Cne (BinrBPF.get_immediate i) Int.zero.

Definition is_not_div_by_zero64 (i: int64) : bool :=
  Int64.cmp Cne (Int64.repr (Int.signed (BinrBPF.get_immediate i))) Int64.zero.

Definition is_shift_range (i: int64) (upper: int): bool :=
  Int.cmpu Clt (BinrBPF.get_immediate i) upper.

Definition is_shift_range64 (i: int64) (upper: int): bool :=
  Int.ltu (Int.repr (Int64.unsigned (Int64.repr (Int.signed (BinrBPF.get_immediate i))))) upper.

Definition bpf_verifier_aux2 (pc len op: nat) (ins: int64) : bool :=
  match nat_to_opcode op with
  | ALU64  (**r 0xX7 / 0xXf *) =>
    match nat_to_opcode_alu op with
    | ALU_DIV => (**r DIV_IMM *) is_well_dst ins && is_not_div_by_zero64 ins
    | ALU_SHIFT => (**r SHIFT_IMM *) is_well_dst ins && is_shift_range64 ins (Int.repr 64%Z)
    | ALU_IMM_Normal => (**r ALU_IMM *) is_well_dst ins
    | ALU_REG_Normal => (**r ALU_REG *) is_well_dst ins && is_well_src ins
    | ALU_ILLEGAL => false
    end
  | ALU32  (**r 0xX4 / 0xXc *) =>
    match nat_to_opcode_alu op with
    | ALU_DIV => (**r DIV_IMM *) is_well_dst ins && is_not_div_by_zero ins
    | ALU_SHIFT => (**r SHIFT_IMM *) is_well_dst ins && is_shift_range ins (Int.repr 32%Z)
    | ALU_IMM_Normal => (**r ALU_IMM *) is_well_dst ins
    | ALU_REG_Normal => (**r ALU_REG *) is_well_dst ins && is_well_src ins
    | ALU_ILLEGAL => false
    end
  | Branch (**r 0xX5 / 0xXd *) =>
    match nat_to_opcode_branch op with
    | JMP_IMM =>
      let ofs := get_offset ins in
        is_well_dst ins && is_well_jump pc len ofs
    | JMP_REG =>
      let ofs := get_offset ins in
        is_well_dst ins && is_well_src ins && is_well_jump pc len ofs
    | JMP_SP => Int.cmpu Ceq (Int.repr (get_dst ins)) (Int.repr 0)
    | JMP_ILLEGAL => false
    end
  | LD_IMM (**r 0xX8 *) =>
    match nat_to_opcode_load_imm op with
    | LD_IMM_Normal  => is_well_dst ins
    | LD_IMM_ILLEGAL => false
    end
  | LD_REG (**r 0xX1/0xX9 *) =>
    match nat_to_opcode_load_reg op with
    | LD_REG_Normal  => is_well_dst ins && is_well_src ins
    | LD_REG_ILLEGAL => false
    end
  | ST_IMM (**r 0xX2/0xXa *) =>
    match nat_to_opcode_store_imm op with
    | ST_IMM_Normal  => is_well_dst ins
    | ST_IMM_ILLEGAL => false
    end
  | ST_REG (**r 0xX3/0xXb *)  =>
    match nat_to_opcode_store_reg op with
    | ST_REG_Normal  => is_well_dst ins && is_well_src ins
    | ST_REG_ILLEGAL => false
    end
  | ILLEGAL => false
  end.

Fixpoint bpf_verifier_aux (pc len: nat) (st: state.state): bool :=
    match pc with
    | O => true
    | S n =>
      let i := List64.MyListIndexs32 (ins st) (Int.repr (Z.of_nat n)) in
      let op := get_opcode i in
        if (bpf_verifier_aux2 n len op i) then
            bpf_verifier_aux n len st
          else
            false
    end.
(*
Fixpoint bpf_verifier_aux_rev (pc len: nat) (st: state.state): bool :=
    match pc with
    | O => true
    | S n =>
      let i := List64.MyListIndexs32 (ins st) (Int.repr (Z.of_nat (len - 1 - n))) in
      let op := get_opcode i in
        if (bpf_verifier_aux2 (len - 1 - n) len op i) then
            bpf_verifier_aux_rev n len st
          else
            false
    end.
*)
Definition bpf_verifier (st: state.state): bool :=
  let len := ins_len st in
  (**r (0, Int.max_unsigned/8): at least one instruction, and at most Int.max_unsigned/8 because of memory region *)
    if negb (Int.ltu (Int.repr (Z.of_nat len)) Int.one) then
      if negb
       (Int.ltu (Int.divu (Int.repr Int.max_unsigned) (Int.repr 8))
          (Int.repr (Z.of_nat len))) then
        if bpf_verifier_aux len len st then
          let i := List64.MyListIndexs32 (ins st) (Int.repr (Z.of_nat  (len - 1))) in
            Int64.eq i (Int64.repr 0x95)
        else
          false
      else
        false
    else
      false.

Lemma sub_lt:
  forall a b,
    b < a ->
    a - 1 - b < a.
Proof.
  intros.
  assert (1+b <= a) by lia.
  rewrite <- Nat.sub_add_distr.
  apply Nat.sub_lt.
  assumption.
  lia.
Qed.

Lemma bpf_verifier_aux_implies:
  forall st pc op ins k
    (Hst: bpf_verifier_aux k (ins_len st) st = true)
    (Hlen: List.length (state.ins st) = ins_len st)
    (Hpc: pc < k)
    (Hop: op = get_opcode ins)
    (Hins: ins = List64.MyListIndexs32 (state.ins st) (Int.repr (Z.of_nat pc))),
      bpf_verifier_aux2 pc (ins_len st) op ins = true.
Proof.
  unfold List64.MyListIndexs32, List64.MyList.index_s32.
  intros.

  induction k.
  - lia.
  - assert (Hpc_eq: pc = k \/ pc < k) by lia.
    destruct Hpc_eq as [Hpc_eq | Hpc_lt].
    + simpl in Hst.
      unfold List64.MyListIndexs32, List64.MyList.index_s32 in Hst.
      rewrite Hpc_eq in *.
      rewrite <- Hins in *.
      match goal with
      | H: (if ?X then _ else _) = _ |- _ =>
        destruct X eqn: Haux2;[ | inversion H]
      end.
      rewrite Hop.
      assumption.
    + apply IHk; auto.
      simpl in Hst.
      match goal with
      | H: (if ?X then _ else _) = _ |- _ =>
        destruct X eqn: Haux2;[ | inversion H]
      end.
      assumption.
Qed.

(*
Lemma is_well_jump_ind:
  forall k len ofs,
    is_well_jump k len ofs = true ->
      is_well_jump 0 len ofs = true.
Proof.
  unfold is_well_jump; intros.
  destruct k.
  - assumption.
  - unfold Int.cmpu in *.
    rewrite Clt_Zlt_iff in *.
    
Qed. *)

Lemma bpf_verifier_aux_implies':
  forall st pc op ins k
    (Hst: bpf_verifier_aux k (ins_len st) st = true)
    (Hlen: List.length (state.ins st) = ins_len st)
    (Hpc: pc < k)
    (Hop: op = get_opcode ins)
    (Hins: ins = List64.MyListIndexs32 (state.ins st) (Int.repr (Z.of_nat (k-1-pc)))),
      bpf_verifier_aux2 (k-1-pc) (ins_len st) op ins = true.
Proof.
  intros.
  assert (H: k-1-pc < k). {
    eapply sub_lt; eauto.
  }
  eapply bpf_verifier_aux_implies; eauto.
Qed.


Lemma bpf_verifier_aux_implies_bpf_verifier_aux:
  forall st pc k
    (Hst: bpf_verifier_aux k (ins_len st) st = true)
    (Hlen: List.length (state.ins st) = ins_len st)
    (Hpc: pc < k),
      bpf_verifier_aux pc (ins_len st) st = true.
Proof.
  intros.
  induction k.
  - lia.
  - assert (Hpc_eq: pc = k \/ pc < k) by lia.
    destruct Hpc_eq as [Hpc_eq | Hpc_lt].
    + simpl in Hst.
      unfold List64.MyListIndexs32, List64.MyList.index_s32 in Hst.
      rewrite Hpc_eq in *.
      match goal with
      | H: (if ?X then _ else _) = _ |- _ =>
        destruct X eqn: Haux2;[ | inversion H]
      end.
      assumption.
    + apply IHk; auto.
      simpl in Hst.
      match goal with
      | H: (if ?X then _ else _) = _ |- _ =>
        destruct X eqn: Haux2;[ | inversion H]
      end.
      assumption.
Qed.


Lemma bpf_verifier_aux_implies_bpf_verifier_aux':
  forall st pc k
    (Hst: bpf_verifier_aux k (ins_len st) st = true)
    (Hlen: List.length (state.ins st) = ins_len st)
    (Hpc: pc < k),
      bpf_verifier_aux (k-1-pc) (ins_len st) st = true.
Proof.
  intros.
  assert (H: k-1-pc < k). {
    eapply sub_lt; eauto.
  }
  eapply bpf_verifier_aux_implies_bpf_verifier_aux; eauto.
Qed.

Lemma bpf_verifier_implies:
  forall st pc op ins
    (Hst: bpf_verifier st = true)
    (Hlen: List.length (state.ins st) = ins_len st)
    (Hpc: pc < ins_len st)
    (Hop: op = get_opcode ins)
    (Hins: ins = List64.MyListIndexs32 (state.ins st) (Int.repr (Z.of_nat pc))),
      bpf_verifier_aux2 pc (ins_len st) op ins = true.
Proof.
  unfold bpf_verifier, List64.MyListIndexs32, List64.MyList.index_s32.
  intros.
  match goal with
  | H: (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Hlen_low;[ | inversion H]
  end.
  match goal with
  | H: (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Hlen_high;[ | inversion H]
  end.
  match goal with
  | H: (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Haux;[ | inversion H]
  end.
  eapply bpf_verifier_aux_implies; eauto.
Qed.

(*
Lemma bpf_verifier_aux_rev_iff:
  forall st k,
    bpf_verifier_aux k (ins_len st) st = bpf_verifier_aux_rev k (ins_len st) st.
Proof.
  intros.
  induction k.
  - simpl. reflexivity.
  - simpl.

    destruct bpf_verifier_aux eqn: Hst; rewrite <-IHk.
    + symmetry in IHk.
      
    + destruct bpf_verifier_aux2; destruct bpf_verifier_aux2; reflexivity.
      

    rewrite Nat.sub_0_r.
    rewrite Nat.sub_diag.
  Search List.rev.
Qed. *)


Close Scope nat_scope.

Lemma verifier_inv_dst_zero:
  forall ins,
    Int.cmpu Ceq (Int.repr (get_dst ins))
              (Int.repr 0) = true ->
      BinrBPF.int64_to_dst_reg' ins = Some R0.
Proof.
  unfold BinrBPF.int64_to_dst_reg', z_to_reg; intros.
  remember (get_dst ins) as i.
  unfold get_dst in Heqi.
  rewrite <- Int64.and_shru in Heqi.
  change (Int64.shru (Int64.repr 4095) (Int64.repr 8)) with (Int64.repr 15) in Heqi.
  rewrite Int64.and_commut in Heqi.
  assert (Hi_le: (0 <= Int64.unsigned
         (Int64.and (Int64.repr 15)
            (Int64.shru ins (Int64.repr 8))) <= (Int64.unsigned (Int64.repr 15)))%Z). {
    split;[ | apply Int64.and_le].
    apply Int64_unsigned_ge_0.
  }
  change (Int64.unsigned (Int64.repr 15)) with 15%Z in Hi_le.
  assert (Hi: (0 <= i <= 15)%Z) by lia.
  clear Heqi Hi_le.
  unfold Int.cmpu in H.
Ltac destruct_if_zeq Hname H :=
  match goal with
  | |- context [(if ?X then _ else _) = Some _] =>
    destruct X eqn: Hname;
    [ rewrite Z.eqb_eq in Hname; rewrite Hname in H; inversion H |
      rewrite Z.eqb_neq in Hname]
  end.
  destruct_if_zeqb Heq0.
  destruct_if_zeq Heq1 H.
  destruct_if_zeq Heq2 H.
  destruct_if_zeq Heq3 H.
  destruct_if_zeq Heq4 H.
  destruct_if_zeq Heq5 H.
  destruct_if_zeq Heq6 H.
  destruct_if_zeq Heq7 H.
  destruct_if_zeq Heq8 H.
  destruct_if_zeq Heq9 H.
  destruct_if_zeq Heq10 H.
  destruct (i =? 11)%Z eqn: H11; 
  [ rewrite Z.eqb_eq in H11; rewrite H11 in H; inversion H |
      rewrite Z.eqb_neq in H11].
  destruct (i =? 12)%Z eqn: H12; 
  [ rewrite Z.eqb_eq in H12; rewrite H12 in H; inversion H |
      rewrite Z.eqb_neq in H12].
  destruct (i =? 13)%Z eqn: H13; 
  [ rewrite Z.eqb_eq in H13; rewrite H13 in H; inversion H |
      rewrite Z.eqb_neq in H13].
  destruct (i =? 14)%Z eqn: H14; 
  [ rewrite Z.eqb_eq in H14; rewrite H14 in H; inversion H |
      rewrite Z.eqb_neq in H14].
  destruct (i =? 15)%Z eqn: H15; 
  [ rewrite Z.eqb_eq in H15; rewrite H15 in H; inversion H |
      rewrite Z.eqb_neq in H15].
  lia.
Qed.


Lemma verifier_inv_is_well_dst:
  forall ins,
    is_well_dst ins = true ->
    exists r,
      BinrBPF.int64_to_dst_reg' ins = Some r.
Proof.
  unfold is_well_dst, BinrBPF.int64_to_dst_reg', z_to_reg; intros.
  remember (get_dst ins) as i.
  unfold get_dst in Heqi.
  rewrite <- Int64.and_shru in Heqi.
  change (Int64.shru (Int64.repr 4095) (Int64.repr 8)) with (Int64.repr 15) in Heqi.
  rewrite Int64.and_commut in Heqi.
  assert (Hi_le: (0 <= Int64.unsigned
         (Int64.and (Int64.repr 15)
            (Int64.shru ins (Int64.repr 8))) <= (Int64.unsigned (Int64.repr 15)))%Z). {
    split;[ | apply Int64.and_le].
    apply Int64_unsigned_ge_0.
  }
  change (Int64.unsigned (Int64.repr 15)) with 15%Z in Hi_le.
  assert (Hi: (0 <= i <= 15)%Z) by lia.
  clear Heqi Hi_le.
  unfold Int.cmpu in H.
  rewrite Cle_Zle_iff in H.
  change (Int.unsigned (Int.repr 10)) with 10%Z in H.
  rewrite Int.unsigned_repr in H; [| change Int.max_unsigned with 4294967295%Z; lia].
  destruct_if_zeqb Heq0.
  destruct_if_zeqb Heq1.
  destruct_if_zeqb Heq2.
  destruct_if_zeqb Heq3.
  destruct_if_zeqb Heq4.
  destruct_if_zeqb Heq5.
  destruct_if_zeqb Heq6.
  destruct_if_zeqb Heq7.
  destruct_if_zeqb Heq8.
  destruct_if_zeqb Heq9.
  destruct_if_zeqb Heq10.
  lia.
Qed.


Lemma verifier_inv_is_well_src:
  forall ins,
    is_well_src ins = true ->
    exists r,
      BinrBPF.int64_to_src_reg' ins = Some r.
Proof.
  unfold is_well_src, BinrBPF.int64_to_src_reg', z_to_reg; intros.
  remember (get_src ins) as i.
  unfold get_src in Heqi.
  rewrite <- Int64.and_shru in Heqi.
  change (Int64.shru (Int64.repr 65535) (Int64.repr 12)) with (Int64.repr 15) in Heqi.
  rewrite Int64.and_commut in Heqi.
  assert (Hi_le: (0 <= Int64.unsigned
         (Int64.and (Int64.repr 15)
            (Int64.shru ins (Int64.repr 12))) <= (Int64.unsigned (Int64.repr 15)))%Z). {
    split;[ | apply Int64.and_le].
    apply Int64_unsigned_ge_0.
  }
  change (Int64.unsigned (Int64.repr 15)) with 15%Z in Hi_le.
  assert (Hi: (0 <= i <= 15)%Z) by lia.
  clear Heqi Hi_le.
  unfold Int.cmpu in H.
  rewrite Cle_Zle_iff in H.
  change (Int.unsigned (Int.repr 10)) with 10%Z in H.
  rewrite Int.unsigned_repr in H; [| change Int.max_unsigned with 4294967295%Z; lia].
  destruct_if_zeqb Heq0.
  destruct_if_zeqb Heq1.
  destruct_if_zeqb Heq2.
  destruct_if_zeqb Heq3.
  destruct_if_zeqb Heq4.
  destruct_if_zeqb Heq5.
  destruct_if_zeqb Heq6.
  destruct_if_zeqb Heq7.
  destruct_if_zeqb Heq8.
  destruct_if_zeqb Heq9.
  destruct_if_zeqb Heq10.
  lia.
Qed.

(*
Lemma verifier_inv_src_reg :
  forall ins,
    well_src ins ->
    exists r,
      BinrBPF.int64_to_src_reg' ins = Some r.
Proof.
  unfold well_src, BinrBPF.int64_to_src_reg'; intros.
  unfold z_to_reg.
  remember (get_src ins) as i.
  clear Heqi.
  destruct_if_zeqb Heq0.
  destruct_if_zeqb Heq1.
  destruct_if_zeqb Heq2.
  destruct_if_zeqb Heq3.
  destruct_if_zeqb Heq4.
  destruct_if_zeqb Heq5.
  destruct_if_zeqb Heq6.
  destruct_if_zeqb Heq7.
  destruct_if_zeqb Heq8.
  destruct_if_zeqb Heq9.
  destruct_if_zeqb Heq10.
  lia.
Qed.
*)
Lemma opcode_and_255:
  forall ins,
    Nat.land (get_opcode ins) 255 = get_opcode ins.
Proof.
  intros.
  unfold get_opcode.
  unfold Int64.and.
  change (Int64.unsigned (Int64.repr 255)) with (Z.of_nat (Z.to_nat 255)).
  assert (Heq: Z.of_nat (Z.to_nat (Int64.unsigned ins)) = Int64.unsigned ins).
  {
    rewrite Z2Nat.id.
    reflexivity.
    apply Int64_unsigned_ge_0.
  }
  rewrite <- Heq; clear Heq.
  rewrite land_land.
  change (Z.to_nat 255) with 255%nat.
  assert (Hrange: (Nat.land (Z.to_nat (Int64.unsigned ins)) 255 <= 255)%nat). {
    rewrite Nat.land_comm.
    rewrite land_bound.
    lia.
  }
  assert (Hrange_z: (Z.of_nat (Nat.land (Z.to_nat (Int64.unsigned ins)) 255%nat) <= 255)%Z) by lia.
  rewrite Int64.unsigned_repr.
  rewrite Nat2Z.id.
  rewrite <- Nat.land_assoc.
  rewrite Nat.land_diag.
  reflexivity.
  change Int64.max_unsigned with 18446744073709551615%Z.
  lia.
Qed.