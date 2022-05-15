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

From compcert Require Import Values Clight Memory Integers.
From Coq Require Import List ZArith.
Import ListNotations.

Fixpoint bind_parameter_temps_s
  (formals : list (AST.ident * Ctypes.type)) (args : list val)
  (le : temp_env) {struct formals} :  temp_env :=
  match formals with
  | [] => le
  | (id, _) :: xl =>
      match args with
      | [] => le
      | v :: vl => bind_parameter_temps_s xl vl (Maps.PTree.set id v le)
      end
  end.

Lemma bind_parameter_temps_eq :
  forall formals args le
         (LEN : List.length formals = List.length args),
    bind_parameter_temps formals args le =
      Some (bind_parameter_temps_s formals args le).
Proof.
  induction formals.
  - simpl. destruct args; try discriminate.
    reflexivity.
  - destruct args ; try discriminate.
    simpl.
    destruct a.
    intros.
    apply IHformals.
    congruence.
Qed.

Lemma unchanged_on_weakP:
  forall m1 m2 (P Q : block -> Z -> Prop)
    (Hunchanged: Mem.unchanged_on (fun b ofs => P b ofs) m1 m2)
    (Himplies: forall b ofs, Q b ofs -> P b ofs),
      Mem.unchanged_on (fun b ofs => Q b ofs) m1 m2.
Proof.
  intros.
  split.
  - destruct Hunchanged as (Hnextblock, _, _).
    assumption.
  - destruct Hunchanged as (_, Hperm, _).
    intros.
    specialize (Himplies b ofs H).
    specialize (Hperm b ofs k p Himplies H0).
    assumption.
  - destruct Hunchanged as (_, _, Hmem_contents).
    intros.
    specialize (Himplies b ofs H).
    specialize (Hmem_contents b ofs Himplies H0).
    assumption.
Qed.

Lemma unchanged_on_weakP_trans:
  forall m1 m2 m3 (P Q R : block -> Z -> Prop)
    (Hunchanged0: Mem.unchanged_on (fun b ofs => P b ofs) m1 m2)
    (Hunchanged1: Mem.unchanged_on (fun b ofs => Q b ofs) m2 m3)
    (Himplies0: forall b ofs, R b ofs -> P b ofs)
    (Himplies1: forall b ofs, R b ofs -> Q b ofs),
      Mem.unchanged_on (fun b ofs => R b ofs) m1 m3.
Proof.
  intros.
  split.
  - destruct Hunchanged0 as (Hnextblock0, _, _).
    destruct Hunchanged1 as (Hnextblock1, _, _).
    eapply Coqlib.Ple_trans; eauto.
  - set (Hunchanged0' := Hunchanged0).
    destruct Hunchanged0' as (_, Hperm0, _).
    destruct Hunchanged1 as (_, Hperm1, _).
    intros.
    specialize (Himplies0 b ofs H).
    specialize (Himplies1 b ofs H).
    specialize (Hperm0 b ofs k p Himplies0 H0).
    eapply Mem.valid_block_unchanged_on in H0; eauto.
    specialize (Hperm1 b ofs k p Himplies1 H0).
    intuition congruence.
  - set (Hunchanged0' := Hunchanged0).
    destruct Hunchanged0' as (_, _, Hmem_contents0).
    destruct Hunchanged1 as (_, _, Hmem_contents1).
    intros.
    specialize (Himplies0 b ofs H).
    specialize (Himplies1 b ofs H).
    specialize (Hmem_contents0 b ofs Himplies0 H0).
    eapply Mem.perm_unchanged_on in H0; eauto.
    specialize (Hmem_contents1 b ofs Himplies1 H0).
    intuition congruence.
Qed.
