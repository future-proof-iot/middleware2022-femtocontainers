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

From compcert Require Import Zbits.
From Coq Require Import Lia ZArith.

(**r Implemented by FB
  a set of useful lemmas about Nat.land
 *)


Ltac simpl_nat :=
  match goal with
  | H: ?X <> ?Y |- context [if (?X =? ?Y) then _ else _] =>
    destruct (X =? Y) eqn: Ht; [rewrite Nat.eqb_eq in Ht; intuition | try reflexivity]; clear Ht
  end.

Open Scope Z_scope.

Fixpoint Forall_exec (P : nat -> bool) (n: nat)  : bool :=
  match n with
  | O => P O
  | S n' => P n && Forall_exec P n'
  end.

Lemma Forall_exec_spec : forall P b,
    Forall_exec P b = true ->
    forall n, (n <= b)%nat -> P n = true.
Proof.
  induction b.
  - simpl. intros.
    assert (n=0%nat) by lia.
    subst. auto.
  - simpl. intros.
    rewrite Bool.andb_true_iff in H.
    assert ( n <= b \/ n = S b)%nat by lia.
    destruct H1 ; subst.
    apply IHb; auto. tauto.
    tauto.
Qed.

Lemma odd_of_nat : forall (n:nat), Z.odd (Z.of_nat n) = Nat.odd n.
Proof.
  intros.
  destruct (Nat.odd n) eqn:NO.
  - rewrite Nat.odd_spec in NO.
    unfold Nat.Odd in NO.
    destruct NO.
    subst.
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_mul.
    rewrite Z.add_comm.
    rewrite Z.odd_add_mul_2.
    reflexivity.
  - destruct (Z.odd (Z.of_nat n)) eqn:ZO; auto.
    rewrite Z.odd_spec in ZO.
    destruct ZO.
    assert (exists m, n = 1 + 2 * m)%nat.
    exists (Z.to_nat x). lia.
    destruct H0.
    subst.
    rewrite Nat.odd_add_mul_2 in NO.
    discriminate.
Qed.

Lemma testbit_of_nat : forall m n,
  Z.testbit (Z.of_nat n) (Z.of_nat m) = Nat.testbit n m.
Proof.
  induction m.
  - intros.
    simpl. apply odd_of_nat.
  - rewrite Nat2Z.inj_succ.
    simpl. intro.
    rewrite <- IHm.
    rewrite Ztestbit_succ by lia.
    f_equal.
    rewrite Nat.div2_div.
    rewrite div_Zdiv by lia.
    lia.
Qed.

Lemma testbit_of_nat_ext : forall i n,
    Z.testbit (Z.of_nat n) i = if Z.leb 0 i
                               then Nat.testbit n (Z.to_nat i)
                               else false.
Proof.
  intros.
  destruct (0 <=? i) eqn:LE.
  -
    apply Zle_bool_imp_le  in LE.
    assert (exists m, Z.of_nat m = i).
    {
      exists (Z.to_nat i).
      lia.
    }
    destruct H as (m & EQ).
    rewrite <- EQ.
    assert (Z.to_nat (Z.of_nat m) = m) by lia.
    rewrite H.
    apply testbit_of_nat.
  - assert (i < 0) by lia.
    destruct i.
    + lia.
    + lia.
    + reflexivity.
Qed.

Lemma land_land : forall n m,
    Z.land (Z.of_nat n) (Z.of_nat m) = Z.of_nat (Nat.land n m).
Proof.
  intros.
  apply Z.bits_inj.
  unfold Z.eqf.
  intros.
  rewrite testbit_of_nat_ext.
  destruct (0 <=? n0) eqn:NO.
  assert (exists i, n0 = Z.of_nat i).
  {
    exists (Z.to_nat n0).
    lia.
  }
  destruct H. subst.
  assert (Z.to_nat (Z.of_nat x) = x) by lia.
  rewrite  H.
  rewrite Z.land_spec.
  rewrite Nat.land_spec.
  rewrite !testbit_of_nat. (**r ? (without natural) performs the rewrite as many times as possible (possibly zero times). This form never fails. ! (without natural) performs the rewrite as many times as possible and at least once. The tactic fails if the requested number of rewrites can't be performed. *)
  reflexivity.
  rewrite Z.land_spec.
  rewrite! testbit_of_nat_ext.
  destruct(0 <=? n0) ; try congruence.
  reflexivity.
Qed.

Close Scope Z_scope.

Lemma land_bound : forall n x, Nat.land n x <= n.
Proof.
  unfold Nat.land.
  intros n x.
  assert (forall n a b, a <= n -> Nat.bitwise andb n a b <= a).
  {
    clear.
    induction n.
    - simpl. lia.
    - intros.
      simpl.
      assert (Nat.bitwise andb n (Nat.div2 a) (Nat.div2 b) <= (Nat.div2 a)).
      {
        apply IHn.
        apply Nat.div2_decr.
        auto.
      }
      revert H0.
      generalize (Nat.bitwise andb n (Nat.div2 a) (Nat.div2 b)) as n1.
      intros.
      rewrite Nat.div2_div in H0.
      rewrite (Nat.div_mod a 2) at 2 by lia.
      assert (a mod 2 = if Nat.odd a then 1 else 0).
      {
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
        rewrite Nat.negb_odd in H1.
        rewrite Nat.even_spec in H1.
        destruct H1 as (x & EQ).
        subst.
        rewrite mult_comm.
        rewrite Nat.mod_mul. reflexivity. lia.
      }
      destruct  (Nat.odd a).
      rewrite H1.
      unfold andb.
      destruct (Nat.odd b) ; lia.
      unfold andb. lia.
  }
  apply H.
  lia.
Qed.

Lemma Nat_land_0xff:
  forall c
    (Hc_le : c <= 255),
      Nat.land c 255 = c.
Proof.
  intros.
  assert (Hc: c < 256) by lia.
  clear Hc_le.
  do 255 (destruct c; [reflexivity |]).
  destruct c; [reflexivity |].
  destruct c;  lia.
Qed.

Lemma Heven_spec:
  forall n, Nat.even n = true -> exists m, n = 2*m.
Proof.
  intros.
  rewrite Nat.even_spec in H.
  rewrite <- Even.even_equiv in H.
  apply Div2.even_2n in H.
  destruct H as (p & Hdouble).
  rewrite Nat.double_twice in Hdouble.
  exists p; assumption.
Qed.

Lemma Hodd_spec :
  forall n, Nat.odd n = true -> exists m, n = 2*m+1.
Proof.
  intros.
  rewrite Nat.odd_spec in H.
  rewrite <- Even.odd_equiv in H.
  apply Div2.odd_S2n in H.
  destruct H as (p & Hdouble).
  rewrite Nat.double_twice in Hdouble.
  rewrite <- Nat.add_1_r in Hdouble.
  exists p; assumption.
Qed.

Lemma nat_land_7_eq_0_intro:
  forall n,
  Nat.land n 7 = 0 -> exists m, n = 0 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - inversion H.
  - rewrite ! Nat.add_0_l in H.
    rewrite ! Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq.
    destruct Hn_eq as (m & Hn_eq).
    clear Hodd.
    subst.
    rewrite ! Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hodd.
    + inversion H.
    + rewrite ! Nat.add_0_l in H.
      rewrite <- Nat.negb_even in Hodd.
      rewrite Bool.negb_false_iff in Hodd.
      apply Heven_spec in Hodd as Hn_eq.
      destruct Hn_eq as (m0 & Hn_eq).
      clear Hodd.
      subst.
      rewrite ! Div2.div2_double in H.
      destruct (Nat.odd m0) eqn: Hodd.
      * inversion H.
      * rewrite <- Nat.negb_even in Hodd.
        rewrite Bool.negb_false_iff in Hodd.
        apply Heven_spec in Hodd as Hn_eq.
        destruct Hn_eq as (m & Hn_eq).
        clear Hodd.
        subst.
        exists m; lia.
Qed.

Lemma nat_land_7_eq_0_elim:
  forall n,
  (exists m, n = 0 + 8 * m) -> Nat.land n 7 = 0.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 0) with false.
  unfold xorb, andb.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold andb.
  rewrite ! Nat.add_0_l.
  rewrite ! Nat.add_0_r.
  assert (Heq: 8 * m = 2 * (4 * m)) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double.
  assert (Heq: 4 * m = 2 * (2 * m)) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold andb.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold andb.
  reflexivity.
Qed.

Lemma nat_land_7_eq_0:
  forall n,
    Nat.land n 7 = 0 <-> exists m, n = 0 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_0_intro.
  apply nat_land_7_eq_0_elim.
Qed.


Lemma nat_land_7_eq_2_intro:
  forall n,
  Nat.land n 7 = 2 -> exists m, n = 2 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - apply Hodd_spec in Hodd as Hn_eq.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Nat.add_0_r in H.
    rewrite Nat.add_1_r in H.
    rewrite ! Div2.div2_double_plus_one in H.
    destruct (Nat.odd m) eqn: Hoddm.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
  - rewrite Nat.add_0_l in H.
    rewrite ! Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq.
    destruct Hn_eq as (m & Hn_eq).
    clear Hodd.
    subst.
    rewrite ! Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hodd.
    + apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite Nat.add_1_r in H.
      rewrite ! Div2.div2_double_plus_one in H.
      destruct (Nat.odd _) eqn: Hodd.
      * inversion H.
      * rewrite <- Nat.negb_even in Hodd.
        rewrite Bool.negb_false_iff in Hodd.
        apply Heven_spec in Hodd as Hn_eq.
        destruct Hn_eq as (m & Hn_eq).
        subst.
        exists m; lia.
    + rewrite Nat.add_0_l in H.
      rewrite <- Nat.negb_even in Hodd.
      rewrite Bool.negb_false_iff in Hodd.
      destruct Nat.odd; inversion H.
Qed.

Lemma nat_land_7_eq_2_elim:
  forall n,
  (exists m, n = 2 + 8 * m) -> Nat.land n 7 = 2.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 2) with false.
  unfold xorb, andb.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold andb.
  assert (Heq: (2 + 8 * m) = 2 * (1 + 4 * m)) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double.
  assert (Heq: 1 + 4 * m = S (2 * (2 * m))) by lia.
  rewrite Heq; clear Heq.
  rewrite Nat.odd_succ.
  rewrite Nat.even_mul.
  change (Nat.even 4) with true.
  unfold orb.
  rewrite ! Nat.add_0_l.
  rewrite ! Nat.add_0_r.
  rewrite Div2.div2_double_plus_one.
  change (Nat.even 2) with true.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold andb.
  reflexivity.
Qed.

Lemma nat_land_7_eq_2:
  forall n,
    Nat.land n 7 = 2 <-> exists m, n = 2 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_2_intro.
  apply nat_land_7_eq_2_elim.
Qed.



Lemma nat_land_7_eq_4_intro:
  forall n,
  Nat.land n 7 = 4 -> exists m, n = 4 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Nat.add_0_r in H.
    rewrite ! Nat.add_1_r in H.
    rewrite ! Div2.div2_double_plus_one in H.
    destruct (Nat.odd m) eqn: Hodd.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
  - rewrite ! Nat.add_0_l in H.
    rewrite ! Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hodd.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + rewrite Nat.add_0_l in H.
      rewrite <- Nat.negb_even in Hodd.
      rewrite Bool.negb_false_iff in Hodd.
      apply Heven_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite ! Div2.div2_double in H.
      destruct (Nat.odd m0) eqn: Hodd.
      * apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
        destruct Hn_eq as (m & Hn_eq).
        subst.
        exists m; lia.
      * inversion H.
Qed.

Lemma nat_land_7_eq_4_elim:
  forall n,
  (exists m, n = 4 + 8 * m) -> Nat.land n 7 = 4.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 4) with false.
  unfold xorb, andb.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold andb.
  assert (Heq: (4 + 8 * m) = 2 * (2 + 4 * m)) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double.
  assert (Heq: 2 + 4 * m = 2 * (1 + 2 * m)) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold andb.
  rewrite ! Nat.add_0_l.
  rewrite ! Nat.add_0_r.
  assert (Heq: (1 + 2 * m) = (S (2*m))) by lia.
  rewrite Heq; clear Heq.
  rewrite Nat.odd_succ.
  rewrite Nat.even_mul.
  change (Nat.even 2) with true.
  unfold orb.
  reflexivity.
Qed.

Lemma nat_land_7_eq_4:
  forall n,
    Nat.land n 7 = 4 <-> exists m, n = 4 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_4_intro.
  apply nat_land_7_eq_4_elim.
Qed.

Lemma nat_land_7_eq_6_intro:
  forall n,
  Nat.land n 7 = 6 -> exists m, n = 6 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Nat.add_0_r in H.
    rewrite ! Nat.add_1_r in H.
    rewrite ! Div2.div2_double_plus_one in H.
    destruct (Nat.odd m) eqn: Hodd.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
  - rewrite ! Nat.add_0_l in H.
    rewrite ! Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hodd.
    + apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite ! Nat.add_1_r in H.
      rewrite ! Div2.div2_double_plus_one in H.
      destruct (Nat.odd _) eqn: Hodd.
      * apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
        destruct Hn_eq as (m & Hn_eq).
        subst.
        exists m; lia.
      * inversion H.
    + rewrite Nat.add_0_l in H.
      destruct (Nat.odd (Nat.div2 m)); inversion H.
Qed.

Lemma nat_land_7_eq_6_elim:
  forall n,
  (exists m, n = 6 + 8 * m) -> Nat.land n 7 = 6.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 6) with false.
  unfold xorb, andb.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold andb.
  assert (Heq: (6 + 8 * m) = 2 * (S (2 * ( S (2 * m))))) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double.
  rewrite Nat.odd_succ.
  rewrite Nat.even_mul.
  change (Nat.even 2) with true.
  unfold orb.
  rewrite ! Nat.add_0_l.
  rewrite Div2.div2_double_plus_one.
  rewrite Nat.odd_succ.
  rewrite Nat.even_mul.
  change (Nat.even 2) with true.
  unfold orb.
  reflexivity.
Qed.

Lemma nat_land_7_eq_6:
  forall n,
    Nat.land n 7 = 6 <-> exists m, n = 6 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_6_intro.
  apply nat_land_7_eq_6_elim.
Qed.

Lemma nat_land_7_eq_1_intro:
  forall n,
  Nat.land n 7 = 1 -> exists m, n = 1 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Nat.add_0_r in H.
    rewrite ! Nat.add_1_r in H.
    rewrite ! Div2.div2_double_plus_one in H.
    destruct (Nat.odd m) eqn: Hodd.
    + inversion H.
    + rewrite Nat.add_0_l in H.
      rewrite <- Nat.negb_even in Hodd.
      rewrite Bool.negb_false_iff in Hodd.
      apply Heven_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite ! Div2.div2_double in H.
      destruct Nat.odd eqn:Hodd.
      * inversion H.
      * rewrite <- Nat.negb_even in Hodd.
        rewrite Bool.negb_false_iff in Hodd.
        apply Heven_spec in Hodd as Hn_eq; clear Hodd.
        destruct Hn_eq as (m & Hn_eq).
        subst.
        exists m; lia.
  - rewrite Nat.add_0_l in H.
    rewrite ! Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hodd.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
Qed.

Lemma nat_land_7_eq_1_elim:
  forall n,
  (exists m, n = 1 + 8 * m) -> Nat.land n 7 = 1.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 1) with true.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold xorb, andb.
  assert (Heq: (1 + 8 * m) = S (2 * (2 * (2 * m)))) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double_plus_one.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold xorb, andb.
  rewrite Div2.div2_double.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold xorb, andb.
  lia.
Qed.

Lemma nat_land_7_eq_1:
  forall n,
    Nat.land n 7 = 1 <-> exists m, n = 1 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_1_intro.
  apply nat_land_7_eq_1_elim.
Qed.

Lemma nat_land_7_eq_3_intro:
  forall n,
  Nat.land n 7 = 3 -> exists m, n = 3 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Nat.add_0_r in H.
    rewrite ! Nat.add_1_r in H.
    rewrite ! Div2.div2_double_plus_one in H.
    destruct (Nat.odd m) eqn: Hodd.
    + apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite ! Nat.add_1_r in H.
      rewrite ! Div2.div2_double_plus_one in H.
      destruct (Nat.odd _) eqn: Hodd.
      * inversion H.
      * rewrite <- Nat.negb_even in Hodd.
        rewrite Bool.negb_false_iff in Hodd.
        apply Heven_spec in Hodd as Hn_eq; clear Hodd.
        destruct Hn_eq as (m & Hn_eq).
        subst.
        exists m; lia.
    + rewrite Nat.add_0_l in H.
      rewrite <- Nat.negb_even in Hodd.
      rewrite Bool.negb_false_iff in Hodd.
      apply Heven_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite ! Div2.div2_double in H.
      destruct Nat.odd eqn:Hodd.
      * inversion H.
      * inversion H.
  - rewrite Nat.add_0_l in H.
    rewrite ! Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hodd.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
Qed.

Lemma nat_land_7_eq_3_elim:
  forall n,
  (exists m, n = 3 + 8 * m) -> Nat.land n 7 = 3.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 3) with true.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold xorb, andb.
  assert (Heq: (3 + 8 * m) = S (2 * (S (2 * (2 * m))))) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double_plus_one.
  rewrite Nat.odd_succ.
  rewrite Nat.even_mul.
  change (Nat.even 2) with true.
  unfold orb.
  rewrite Div2.div2_double_plus_one.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold andb.
  lia.
Qed.

Lemma nat_land_7_eq_3:
  forall n,
    Nat.land n 7 = 3 <-> exists m, n = 3 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_3_intro.
  apply nat_land_7_eq_3_elim.
Qed.

Lemma nat_land_7_eq_5_intro:
  forall n,
  Nat.land n 7 = 5 -> exists m, n = 5 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Nat.add_0_r in H.
    rewrite ! Nat.add_1_r in H.
    rewrite ! Div2.div2_double_plus_one in H.
    destruct (Nat.odd m) eqn: Hodd.
    + apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite ! Nat.add_1_r in H.
      rewrite ! Div2.div2_double_plus_one in H.
      destruct (Nat.odd _) eqn: Hodd.
      * inversion H.
      * inversion H.
    + rewrite Nat.add_0_l in H.
      rewrite <- Nat.negb_even in Hodd.
      rewrite Bool.negb_false_iff in Hodd.
      apply Heven_spec in Hodd as Hn_eq; clear Hodd.
      destruct Hn_eq as (m0 & Hn_eq).
      subst.
      rewrite ! Div2.div2_double in H.
      destruct Nat.odd eqn:Hodd.
      * apply Hodd_spec in Hodd as Hn_eq; clear Hodd.
        destruct Hn_eq as (m & Hn_eq).
        subst.
        exists m; lia.
      * inversion H.
  - rewrite Nat.add_0_l in H.
    rewrite ! Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq; clear Hodd.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    rewrite ! Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hodd.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
Qed.

Lemma nat_land_7_eq_5_elim:
  forall n,
  (exists m, n = 5 + 8 * m) -> Nat.land n 7 = 5.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 5) with true.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold xorb, andb.
  assert (Heq: (5 + 8 * m) = S (2 * (2 * (S (2 * m))))) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double_plus_one.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold andb.
  rewrite Div2.div2_double.
  rewrite Nat.odd_succ.
  rewrite Nat.even_mul.
  change (Nat.even 2) with true.
  unfold orb.
  lia.
Qed.

Lemma nat_land_7_eq_5:
  forall n,
    Nat.land n 7 = 5 <-> exists m, n = 5 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_5_intro.
  apply nat_land_7_eq_5_elim.
Qed.

Lemma nat_land_7_eq_7_intro:
  forall n,
  Nat.land n 7 = 7 -> exists m, n = 7 + 8 * m.
Proof.
  intros.
  rewrite Nat.land_comm in H.
  unfold Nat.land in H.
  simpl in H.
  destruct (Nat.odd n) eqn: Hodd.
  - apply Hodd_spec in Hodd as Hn_eq.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    repeat rewrite Nat.add_0_r in H.
    rewrite Nat.add_1_r in H.
    repeat rewrite Div2.div2_double_plus_one in H.
    destruct (Nat.odd m) eqn: Hoddm.
    + apply Hodd_spec in Hoddm as Hm_eq.
      destruct Hm_eq as (m0 & Hm_eq).
      subst.
      rewrite Nat.add_1_r in H.
      repeat rewrite Div2.div2_double_plus_one in H.
      destruct (Nat.odd m0) eqn: Hoddm0.
      * apply Hodd_spec in Hoddm0 as Hm0_eq.
        destruct Hm0_eq as (m & Hm_eq).
        subst.
        exists m.
        lia.
      * inversion H.
    + rewrite Nat.add_0_l in H.
      destruct (Nat.odd (Nat.div2 _)); inversion H.
  - rewrite Nat.add_0_l in H.
    repeat rewrite Nat.add_0_r in H.
    rewrite <- Nat.negb_even in Hodd.
    rewrite Bool.negb_false_iff in Hodd.
    apply Heven_spec in Hodd as Hn_eq.
    destruct Hn_eq as (m & Hn_eq).
    subst.
    repeat rewrite Div2.div2_double in H.
    destruct (Nat.odd m) eqn: Hoddm.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
    + destruct (Nat.odd (Nat.div2 _)); inversion H.
Qed.

Lemma nat_land_7_eq_7_elim:
  forall n,
  (exists m, n = 7 + 8 * m) -> Nat.land n 7 = 7.
Proof.
  intros.
  destruct H as (m & H).
  rewrite Nat.land_comm.
  unfold Nat.land.
  simpl.
  subst.
  rewrite Nat.odd_add.
  change (Nat.odd 7) with true.
  rewrite Nat.odd_mul.
  change (Nat.odd 8) with false.
  unfold xorb, andb.
  assert (Heq: (7 + 8 * m) = (S (2 *(3+4*m)))) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double_plus_one.
  rewrite Nat.odd_add.
  change (Nat.odd 3) with true.
  rewrite Nat.odd_mul.
  change (Nat.odd 4) with false.
  unfold xorb, andb.
  assert (Heq: (3 + 4 * m) = (S (2 *(1+2*m)))) by lia.
  rewrite Heq; clear Heq.
  rewrite Div2.div2_double_plus_one.
  rewrite Nat.odd_add.
  change (Nat.odd 1) with true.
  rewrite Nat.odd_mul.
  change (Nat.odd 2) with false.
  unfold xorb, andb.
  lia.
Qed.

Lemma nat_land_7_eq_7:
  forall n,
    Nat.land n 7 = 7 <-> exists m, n = 7 + 8 * m.
Proof.
  intros.
  split.
  apply nat_land_7_eq_7_intro.
  apply nat_land_7_eq_7_elim.
Qed.

Lemma nat_land_7_eq:
  forall n k
    (Hrange: k <= 7),
      Nat.land n 7 = k <-> exists m, n = k + 8 * m.
Proof.
  intros.
  destruct k; [apply nat_land_7_eq_0 | ].
  destruct k; [apply nat_land_7_eq_1 | ].
  destruct k; [apply nat_land_7_eq_2 | ].
  destruct k; [apply nat_land_7_eq_3 | ].
  destruct k; [apply nat_land_7_eq_4 | ].
  destruct k; [apply nat_land_7_eq_5 | ].
  destruct k; [apply nat_land_7_eq_6 | ].
  destruct k; [apply nat_land_7_eq_7 | ].
  lia.
Qed.