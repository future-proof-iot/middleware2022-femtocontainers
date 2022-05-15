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
From bpf.comm Require Import LemmaNat.
From bpf.monadicmodel Require Import Opcode.
From Coq Require Import Lia ZArith List.
Import ListNotations.

Open Scope Z_scope.

Lemma nat8_land_240_255_eq:
  forall (n:nat)
    (Hnat8: (n <= 255)%nat),
    (Int.and (Int.and (Int.repr (Z.of_nat n)) (Int.repr 240)) (Int.repr 255)) = Int.repr (Z.of_nat (Nat.land n 240)).
Proof.
  intros.
  rewrite Int.and_assoc.
  change (Int.and (Int.repr 240) (Int.repr 255)) with (Int.repr 240).
  unfold Int.and.
  f_equal.
  rewrite! Int.unsigned_repr_eq.
  change (240 mod Int.modulus) with 240.
  rewrite Zmod_small.
  change 240 with (Z.of_nat 240%nat).
  rewrite land_land. reflexivity.
  change Int.modulus with 4294967296.
  lia.
Qed.

Open Scope nat_scope.
Definition byte_to_opcode_alu64_if (op: nat): opcode_alu64 :=
  let opcode_alu := Nat.land op 0xf0 in (**r masking operation *)
    if opcode_alu =? 0x00 then op_BPF_ADD64
    else if opcode_alu =? 0x10 then op_BPF_SUB64
    else if opcode_alu =? 0x20 then op_BPF_MUL64
    else if opcode_alu =? 0x30 then op_BPF_DIV64
    else if opcode_alu =? 0x40 then op_BPF_OR64
    else if opcode_alu =? 0x50 then op_BPF_AND64
    else if opcode_alu =? 0x60 then op_BPF_LSH64
    else if opcode_alu =? 0x70 then op_BPF_RSH64
    else if opcode_alu =? 0x80 then op_BPF_NEG64
    else if opcode_alu =? 0x90 then op_BPF_MOD64
    else if opcode_alu =? 0xa0 then op_BPF_XOR64
    else if opcode_alu =? 0xb0 then op_BPF_MOV64
    else if opcode_alu =? 0xc0 then op_BPF_ARSH64
    else op_BPF_ALU64_ILLEGAL_INS
  .

Lemma opcode_alu64_eqb_eq : forall a b,
    opcode_alu64_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_alu64 :
  forall (E: nat -> opcode_alu64)
         (F: nat -> opcode_alu64) n,
    ((fun n => opcode_alu64_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_alu64_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_alu64_if_same:
  forall (op: nat),
    byte_to_opcode_alu64 op = byte_to_opcode_alu64_if op.
Proof.
  intros.
  unfold byte_to_opcode_alu64, byte_to_opcode_alu64_if.
  apply opcode_alu64_eqb_eq.
  match goal with
  | |- ?A = true => set (P := A)
  end.
  pattern (Nat.land op 240) in P.
  match goal with
  | P := ?F (Nat.land op 240) |- _=>
      apply (Forall_exec_spec F 240)
  end.
  destruct (op =? 135).
  vm_compute.
  reflexivity.
  vm_compute.
  reflexivity.
  rewrite Nat.land_comm.
  apply land_bound.
Qed.

Lemma byte_to_opcode_alu64_if_default:
  forall op
    (Hadd: Nat.land op 240 <> 0x00)
    (Hsub: Nat.land op 240 <> 0x10)
    (Hmul: Nat.land op 240 <> 0x20)
    (Hdiv: Nat.land op 240 <> 0x30)
    (Hor:  Nat.land op 240 <> 0x40)
    (Hand: Nat.land op 240 <> 0x50)
    (Hlsh: Nat.land op 240 <> 0x60)
    (Hrsh: Nat.land op 240 <> 0x70)
    (Hneg: Nat.land op 240 <> 0x80)
    (Hmod: Nat.land op 240 <> 0x90)
    (Hxor: Nat.land op 240 <> 0xa0)
    (Hmov: Nat.land op 240 <> 0xb0)
    (Harsh: Nat.land op 240 <> 0xc0),
      byte_to_opcode_alu64_if op = op_BPF_ALU64_ILLEGAL_INS.
Proof.
  intros.
  unfold byte_to_opcode_alu64_if.
  repeat simpl_nat.
Qed.

Definition byte_to_opcode_alu32_if (op: nat): opcode_alu32 :=
  let opcode_alu := Nat.land op 0xf0 in (**r masking operation *)
    if opcode_alu =? 0x00 then op_BPF_ADD32
    else if opcode_alu =? 0x10 then op_BPF_SUB32
    else if opcode_alu =? 0x20 then op_BPF_MUL32
    else if opcode_alu =? 0x30 then op_BPF_DIV32
    else if opcode_alu =? 0x40 then op_BPF_OR32
    else if opcode_alu =? 0x50 then op_BPF_AND32
    else if opcode_alu =? 0x60 then op_BPF_LSH32
    else if opcode_alu =? 0x70 then op_BPF_RSH32
    else if opcode_alu =? 0x80 then op_BPF_NEG32 (*
    else if opcode_alu =? 0x80 then if Nat.eqb op 0x84 then op_BPF_NEG32 else op_BPF_ALU32_ILLEGAL_INS *)
    else if opcode_alu =? 0x90 then op_BPF_MOD32
    else if opcode_alu =? 0xa0 then op_BPF_XOR32
    else if opcode_alu =? 0xb0 then op_BPF_MOV32
    else if opcode_alu =? 0xc0 then op_BPF_ARSH32
    else op_BPF_ALU32_ILLEGAL_INS
  .

Lemma opcode_alu32_eqb_eq : forall a b,
    opcode_alu32_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_alu32 :
  forall (E: nat -> opcode_alu32)
         (F: nat -> opcode_alu32) n,
    ((fun n => opcode_alu32_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_alu32_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_alu32_if_same:
  forall (op: nat),
    byte_to_opcode_alu32 op = byte_to_opcode_alu32_if op.
Proof.
  intros.
  unfold byte_to_opcode_alu32, byte_to_opcode_alu32_if.
  apply opcode_alu32_eqb_eq.
  match goal with
  | |- ?A = true => set (P := A)
  end.
  pattern (Nat.land op 240) in P.
  match goal with
  | P := ?F (Nat.land op 240) |- _=>
      apply (Forall_exec_spec F 240)
  end.
  destruct (op =? 132).
  vm_compute.
  reflexivity.
  vm_compute.
  reflexivity.
  rewrite Nat.land_comm.
  apply land_bound.
Qed.

Lemma byte_to_opcode_alu32_if_default:
  forall op
    (Hadd: Nat.land op 240 <> 0x00)
    (Hsub: Nat.land op 240 <> 0x10)
    (Hmul: Nat.land op 240 <> 0x20)
    (Hdiv: Nat.land op 240 <> 0x30)
    (Hor:  Nat.land op 240 <> 0x40)
    (Hand: Nat.land op 240 <> 0x50)
    (Hlsh: Nat.land op 240 <> 0x60)
    (Hrsh: Nat.land op 240 <> 0x70)
    (Hneg: Nat.land op 240 <> 0x80)
    (Hmod: Nat.land op 240 <> 0x90)
    (Hxor: Nat.land op 240 <> 0xa0)
    (Hmov: Nat.land op 240 <> 0xb0)
    (Harsh: Nat.land op 240 <> 0xc0),
      byte_to_opcode_alu32_if op = op_BPF_ALU32_ILLEGAL_INS.
Proof.
  intros.
  unfold byte_to_opcode_alu32_if.
  repeat simpl_nat.
Qed.

Definition byte_to_opcode_branch_if (op: nat): opcode_branch :=
  let opcode_alu := Nat.land op 0xf0 in (**r masking operation *)
    if opcode_alu =? 0x00 then op_BPF_JA (*
    if opcode_alu =? 0x00 then if Nat.eqb op 0x05 then op_BPF_JA else op_BPF_JMP_ILLEGAL_INS *)
    else if opcode_alu =? 0x10 then op_BPF_JEQ
    else if opcode_alu =? 0x20 then op_BPF_JGT
    else if opcode_alu =? 0x30 then op_BPF_JGE
    else if opcode_alu =? 0xa0 then op_BPF_JLT
    else if opcode_alu =? 0xb0 then op_BPF_JLE
    else if opcode_alu =? 0x40 then op_BPF_JSET
    else if opcode_alu =? 0x50 then op_BPF_JNE
    else if opcode_alu =? 0x60 then op_BPF_JSGT
    else if opcode_alu =? 0x70 then op_BPF_JSGE
    else if opcode_alu =? 0xc0 then op_BPF_JSLT
    else if opcode_alu =? 0xd0 then op_BPF_JSLE
    else if opcode_alu =? 0x80 then op_BPF_CALL
    else if opcode_alu =? 0x90 then op_BPF_RET (*
    else if opcode_alu =? 0x80 then if Nat.eqb op 0x85 then op_BPF_CALL else op_BPF_JMP_ILLEGAL_INS
    else if opcode_alu =? 0x90 then if Nat.eqb op 0x95 then op_BPF_RET else op_BPF_JMP_ILLEGAL_INS *)
    else op_BPF_JMP_ILLEGAL_INS
  .

Lemma opcode_branch_eqb_eq : forall a b,
    opcode_branch_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_branch :
  forall (E: nat -> opcode_branch)
         (F: nat -> opcode_branch) n,
    ((fun n => opcode_branch_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_branch_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_branch_if_same:
  forall (op: nat),
    byte_to_opcode_branch op = byte_to_opcode_branch_if op.
Proof.
  intros.
  unfold byte_to_opcode_branch, byte_to_opcode_branch_if.
  apply opcode_branch_eqb_eq.
  match goal with
  | |- ?A = true => set (P := A)
  end.
  pattern (Nat.land op 240) in P.
  match goal with
  | P := ?F (Nat.land op 240) |- _=>
      apply (Forall_exec_spec F 240)
  end.
  destruct (op =? 5); destruct (op =? 133); destruct (op =? 149).
  all: try (vm_compute; reflexivity).
  rewrite Nat.land_comm.
  apply land_bound.
Qed.

Lemma List_in_tl:
  forall (A:Type) (a b: Type) tl
    (Hneq : a <> b)
    (Hin : List.In a (b :: tl)),
      List.In a tl.
Proof.
  intros.
  simpl in Hin.
  destruct Hin as [Heq | Hin].
  - intuition.
  - assumption.
Qed.

Lemma mod2_odd:
  forall a, a mod 2 = if Nat.odd a then 1 else 0.
Proof.
  intros.
  destruct (Nat.odd a) eqn:O.
  apply Nat.odd_spec in O.
  unfold Nat.Odd in O.
  destruct O as (m & E).
  subst.
  replace (2 * m + 1) with (1 + m * 2) by lia.
  rewrite Nat.mod_add. reflexivity.
  lia.
  assert (negb (Nat.odd a) = true).
  { rewrite O; reflexivity. }
  rewrite Nat.negb_odd in H.
  rewrite Nat.even_spec in H.
  destruct H as (x & EQ).
  subst.
  rewrite mult_comm.
  rewrite Nat.mod_mul. reflexivity. lia.
Qed.

(*
Lemma nat_land_0xf0_eq_0x00:
  forall n,
    Nat.land n 240 = 0 ->
      n = 0x07 \/ n = 0x0f.
Proof.
  intros.
  Search (Nat.land _ _ = _).
  rewrite Nat.land_comm in H.
  unfold Nat.land in H. Search Nat.bitwise.
Qed. *)

Lemma nat_land_240_eq_128:
  forall n
    (Hrange : n <= 255)
    (Hland7: Nat.land n 7 = 7),
      Nat.land n 240 = 128 <-> n = 0x87 \/ n =0x8f.
Proof.
  intros.
  split; intro.
  - (*rewrite Nat.land_comm in H.*)
    unfold Nat.land in H.
    rewrite nat_land_7_eq in Hland7.
    destruct Hland7 as (m & Hland7).
    assert (Heq: 7 + 8 * m = S (2 *(S (2 *(S (2*m)))))) by lia.
    rewrite Heq in Hland7; clear Heq.
    remember (2 * S (2 * S (2 * m))) as m'.
    rewrite Hland7 in H.
    simpl in H.
    rewrite Heqm' in H.
    change (Nat.odd 240) with false in H;
    rewrite Bool.andb_false_r in H.
    assert (Heq: 2 * S (2 * S (2 * m)) = S (S (2* (2 *(S (2 * m)))))) by lia.
    rewrite Heq in H; clear Heq.
    rewrite Nat.div2_succ_double in H.
    rewrite Nat.add_0_r, Nat.add_0_l in H.
    assert (Heq_64: Nat.bitwise andb (S (S (2 * (2 * S (2 * m))))) (S (2 * S (2 * m))) 120 = 64) by lia.
    clear H. rename Heq_64 into H.
    remember (2 * S (2 * m)) as m1.
    simpl in H.
    repeat rewrite Bool.andb_false_r in H.
    repeat rewrite Nat.add_0_r, Nat.add_0_l in H.
    remember (Nat.bitwise andb (m1 + m1)
        (Nat.div2 match m1 with
                  | 0 => 0
                  | S n' => S (Nat.div2 n')
                  end) 30) as nat_and.
    assert (Heq: nat_and = 16) by lia.
    clear H. rename Heq into H.
    subst.
    assert (Heq0: 2 * S (2 * m) = S (S (2 * (2 *m)))) by lia.
    rewrite Heq0 in H; clear Heq0.
    repeat rewrite Nat.div2_succ_double in H.
    assert (Heq0: (S (S (2 * (2 * m))) + S (S (2 * (2 * m)))) = S ( S( 2 *(S (2 * (2 * m)))))) by lia.
    rewrite Heq0 in H; clear Heq0.
    remember (2 * S (2 * (2 * m))) as m1.
    simpl in H.

    rewrite Bool.andb_false_r in H;
    rewrite Nat.add_0_l in H;
    repeat rewrite Nat.add_0_r in H.
    remember (Nat.bitwise andb m1 (Nat.div2 (Nat.div2 m)) 7) as nat_land4.
    rewrite Bool.andb_true_r in H.
    destruct (Nat.even m) eqn: Heven.
    + apply Heven_spec in Heven as Hn_eq.
      destruct Hn_eq as (m0 & Hn_eq).
      subst m.
      destruct (Nat.even m0) eqn: Heven0.
      * apply Heven_spec in Heven0 as Hn_eq.
        destruct Hn_eq as (m2 & Hn_eq).
        subst m0.
        rewrite Nat.div2_double in H.
        rewrite Nat.odd_mul in H.
        rewrite Bool.andb_false_l in H.
        assert (Heq: nat_land4 = 4) by lia.
        clear H; rename Heq into H; subst.
        repeat rewrite Nat.div2_double in H.
        assert (Heq: (2 * S (2 * (2 * (2 * (2 * m2))))) = S (S (2 * (2 * (2 * (2 * (2 * m2))))))) by lia.
        rewrite Heq in H; clear Heq.
        remember (2 * (2 * (2 * (2 * (2 * m2))))) as m1.
        simpl in H.
        remember (Nat.bitwise andb m1 (Nat.div2 (Nat.div2 m2)) 1) as nat_land.
        repeat rewrite Bool.andb_true_r in H.
        destruct (Nat.even m2) eqn: Heven2.
        {
          apply Heven_spec in Heven2 as Hn_eq.
          destruct Hn_eq as (m3 & Hn_eq).
          subst m2.
          destruct (Nat.even m3) eqn: Heven3.
          {
            apply Heven_spec in Heven3 as Hn_eq.
            destruct Hn_eq as (m4 & Hn_eq).
            subst m3.
            repeat rewrite Nat.div2_double in H.
            repeat rewrite Nat.odd_mul in H.
            repeat rewrite Bool.andb_false_l in H.
            assert (Heq: nat_land = 1) by lia.
            rewrite Heqnat_land in Heq; clear Heqnat_land.
            repeat rewrite Nat.div2_double in Heq.
            clear H; rename Heq into H; subst.
            left.
            destruct m4.
            inversion H.
            destruct m4.
            reflexivity.
            lia.
          }
          {
            rewrite <- Nat.negb_odd in Heven3.
            rewrite Bool.negb_false_iff in Heven3.
            apply Hodd_spec in Heven3 as Hn_eq.
            destruct Hn_eq as (m4 & Hn_eq).
            rewrite Nat.add_1_r in Hn_eq.
            subst m3.
            rewrite Nat.div2_double in *.
            rewrite Nat.odd_succ in H.
            rewrite Nat.odd_mul in H.
            rewrite Nat.even_mul in H.
            simpl in H.
            lia.
          }
        }
        {
          rewrite <- Nat.negb_odd in Heven2.
          rewrite Bool.negb_false_iff in Heven2.
          apply Hodd_spec in Heven2 as Hn_eq.
          destruct Hn_eq as (m3 & Hn_eq).
          rewrite Nat.add_1_r in Hn_eq.
          subst m2.
          rewrite Nat.div2_succ_double in *.
          rewrite Nat.odd_succ in H.
          rewrite Nat.even_mul in H.
          simpl in H.
          lia.
        }
      * rewrite <- Nat.negb_odd in Heven0.
        rewrite Bool.negb_false_iff in Heven0.
        apply Hodd_spec in Heven0 as Hn_eq.
        destruct Hn_eq as (m2 & Hn_eq).
        rewrite Nat.add_1_r in Hn_eq.
        subst m0.
        rewrite Nat.div2_double in *.
        rewrite Nat.odd_succ in H.
        rewrite Nat.even_mul in H.
        simpl in H.
        lia.
    + rewrite <- Nat.negb_odd in Heven.
      rewrite Bool.negb_false_iff in Heven.
      apply Hodd_spec in Heven as Hn_eq.
      destruct Hn_eq as (m0 & Hn_eq).
      rewrite Nat.add_1_r in Hn_eq.
      subst m.
      rewrite Nat.div2_succ_double in *.
      destruct (Nat.odd m0) eqn: Hodd.
      * apply Hodd_spec in Hodd as Hn_eq.
        destruct Hn_eq as (m2 & Hn_eq).
        subst m0.
        lia.
      * rewrite <- Nat.negb_even in Hodd.
        rewrite Bool.negb_false_iff in Hodd.
        apply Heven_spec in Hodd as Hn_eq.
        destruct Hn_eq as (m2 & Hn_eq).
        subst m0.
        assert (Heq: nat_land4 = 4) by lia.
        clear H; rename Heq into H; subst.

        repeat rewrite Nat.div2_double in H.
        assert (Heq: (2 * S (2 * (2 * S (2 * (2 * m2))))) = S (S (2 * (2 * (2 * S (2 * (2 * m2))))))) by lia.
        rewrite Heq in H; clear Heq.
        remember (2 * (2 * (2 * S (2 * (2 * m2))))) as m1.
        simpl in H.
        remember (Nat.bitwise andb m1 (Nat.div2 (Nat.div2 m2)) 1) as nat_land.
        repeat rewrite Bool.andb_true_r in H.
        destruct (Nat.even m2) eqn: Heven2.
        {
          apply Heven_spec in Heven2 as Hn_eq.
          destruct Hn_eq as (m3 & Hn_eq).
          subst m2.
          destruct (Nat.even m3) eqn: Heven3.
          {
            apply Heven_spec in Heven3 as Hn_eq.
            destruct Hn_eq as (m4 & Hn_eq).
            subst m3.
            repeat rewrite Nat.div2_double in H.
            repeat rewrite Nat.odd_mul in H.
            repeat rewrite Bool.andb_false_l in H.
            assert (Heq: nat_land = 1) by lia.
            rewrite Heqnat_land in Heq; clear Heqnat_land.
            repeat rewrite Nat.div2_double in Heq.
            clear H; rename Heq into H; subst.
            right.
            destruct m4.
            inversion H.
            destruct m4.
            reflexivity.
            lia.
          }
          {
            rewrite <- Nat.negb_odd in Heven3.
            rewrite Bool.negb_false_iff in Heven3.
            apply Hodd_spec in Heven3 as Hn_eq.
            destruct Hn_eq as (m4 & Hn_eq).
            rewrite Nat.add_1_r in Hn_eq.
            subst m3.
            rewrite Nat.div2_double in *.
            rewrite Nat.odd_succ in H.
            rewrite Nat.odd_mul in H.
            rewrite Nat.even_mul in H.
            simpl in H.
            lia.
          }
        }
        {
          rewrite <- Nat.negb_odd in Heven2.
          rewrite Bool.negb_false_iff in Heven2.
          apply Hodd_spec in Heven2 as Hn_eq.
          destruct Hn_eq as (m3 & Hn_eq).
          rewrite Nat.add_1_r in Hn_eq.
          subst m2.
          rewrite Nat.div2_succ_double in *.
          rewrite Nat.odd_succ in H.
          rewrite Nat.even_mul in H.
          simpl in H.
          lia.
        }
      + lia.
  - destruct H; subst; reflexivity.
Qed.

Lemma nat8_neq_k:
  forall n k
    (Hn_range : n <= 255)
    (Hk_range : (0 <= k <= 255)%Z)
    (Hc2_eq : (Z.of_nat n) <> k),
      Int.repr (Z.of_nat n) <> Int.repr k.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  all: change Int.modulus with 4294967296%Z; lia.
Qed.

(*
Lemma nat8_neq_135:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 135),
      Int.repr (Z.of_nat n) <> Int.repr 135.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  change Int.modulus with 4294967296%Z.
  lia.
Qed.

Lemma nat8_neq_5:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 5),
      Int.repr (Z.of_nat n) <> Int.repr 5.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  change Int.modulus with 4294967296%Z.
  lia.
Qed.


Lemma nat8_neq_133:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 133),
      Int.repr (Z.of_nat n) <> Int.repr 133.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  change Int.modulus with 4294967296%Z.
  lia.
Qed.

Lemma nat8_neq_149:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 149),
      Int.repr (Z.of_nat n) <> Int.repr 149.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  change Int.modulus with 4294967296%Z.
  lia.
Qed.
*)

Lemma nat_odd_S:
  forall n,
  Nat.odd (S n) = negb (Nat.odd n).
Proof.
  intros.
  destruct (Nat.odd n) eqn: Hodd.
  - rewrite <- Nat.negb_even in Hodd.
    rewrite Nat.odd_succ.
    rewrite Bool.negb_true_iff in Hodd.
    rewrite Hodd; reflexivity.
  - rewrite <- Nat.negb_even in Hodd.
    rewrite Nat.odd_succ.
    rewrite Bool.negb_false_iff in Hodd.
    rewrite Hodd; reflexivity.
Qed.

Ltac simpl_if Ht :=
  match goal with
  | |- context [if ?X then _ else _] =>
    destruct X eqn: Ht; [rewrite Nat.eqb_eq in Ht | rewrite Nat.eqb_neq in Ht]
  end.


Ltac disj_true :=
  match goal with
  | |- Vint (Int.repr (Z.of_nat ?X)) = Vint (Int.repr (Z.of_nat ?Y)) =>
    let t := (eval compute in (Nat.eqb X Y)) in
      match t with
      | true => replace Y with X; reflexivity
      | false => fail "disjoint false"
      end
  | |- Vint (Int.repr (Z.of_nat ?X)) = Vint (Int.repr (Z.of_nat ?Y)) \/ _ =>
    let t := (eval compute in (Nat.eqb X Y)) in
      match t with
      | true => left; replace Y with X; reflexivity
      | false => right; disj_true
      end
  end.

Ltac simpl_opcode Hop := simpl_if Hop; [rewrite Hop; disj_true | ].

Ltac simpl_land HOP:=
  match goal with
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y <> ?W) /\ _ =>
      split; [intro HOP; rewrite H in HOP; inversion HOP |]
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y = ?W -> _) /\ _ =>
      split; [intro HOP; rewrite H in HOP; inversion HOP |]
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y <> ?W) =>
      intro HOP; rewrite H in HOP; inversion HOP
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y = ?W -> _) =>
      intro HOP; rewrite H in HOP; inversion HOP
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y <> ?Z) /\ _ =>
      split; [assumption |]
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y <> ?Z) =>
      assumption
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y = ?Z -> _) /\ _ =>
      split; [intro HOP; rewrite HOP in H; exfalso; apply H; reflexivity |]
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y = ?Z -> _) =>
      intro HOP; rewrite HOP in H; exfalso; apply H; reflexivity
  end.

Close Scope Z_scope.