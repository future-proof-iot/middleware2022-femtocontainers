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

From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import MatchState InterpreterRel.

(*
Check get_mem_region.

get_mem_region
     : nat -> MyMemRegionsType -> M memory_region *)

Section Get_mem_region.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [(nat:Type); (list memory_region:Type)].
  Definition res : Type := (memory_region:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_mem_region.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_mem_region.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
      (dcons (fun x => StateLess _ (nat_correct x))
        (dcons (fun x => StateFull _ (mrs_correct S x))
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun r  => StateFull _ (mr_correct r).

Lemma memory_region_in_nth_error:
  forall n l
    (Hrange : (0 <= Z.of_nat n < Z.of_nat (List.length l))%Z),
      exists (m:memory_region), nth_error l n = Some m.
Proof.
  intros.
  destruct Hrange as (Hlow & Hhigh).
  rewrite <- Nat2Z.inj_lt in Hhigh.
  rewrite <- List.nth_error_Some in Hhigh.
  destruct (nth_error l n).
  - exists m; reflexivity.
  - exfalso; apply Hhigh; reflexivity.
Qed.


  Instance correct_function_get_mem_region : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    unfold INV.
    unfold f.
    repeat intro; simpl.
    destruct get_mem_region eqn: Hregion; [|constructor].
    destruct p0.
    intros.
    get_invariant _n.
    get_invariant _mrs.

    unfold eval_inv, nat_correct in c1.
    unfold eval_inv, mrs_correct, match_regions in c2.
    destruct c1 as (c1 & _).
    destruct c2 as (Hv0_eq & Hmrs_eq & (Hmrs_num_eq & Hrange & Hmatch) & Hst).
    subst.
    assert (MOD : m = m /\ st = s).
    {
      unfold get_mem_region in Hregion.
      destruct (c <? mrs_num st)%nat ; try discriminate.
      destruct (nth_error (bpf_mrs st) c); try congruence.
      intuition congruence.
    }
    destruct MOD ; subst.
    eexists; exists m, Events.E0.
    split_and; auto.
    - {
      unfold step2.
      repeat forward_star.
    }
    -
    unfold get_mem_region in Hregion.
    context_destruct_if_inversion.
    rewrite Nat.ltb_lt in Hcond.
    unfold match_list_region in Hmatch.
    rewrite Hmrs_num_eq in Hmatch.
    assert (HrangeNat: (0 <= c < mrs_num s)%nat) by lia.
    specialize (Hmatch c HrangeNat).
    (**r because 0<=c < length mrs, so we know nth_error must return Some mr *)
    assert (HrangeZ: (0 <= Z.of_nat c < Z.of_nat (mrs_num s))%Z) by lia.
    rewrite <- Hmrs_num_eq in HrangeZ.
    apply memory_region_in_nth_error with (n:=c) (l:= bpf_mrs s) in HrangeZ as Hnth_error.
    destruct Hnth_error as (mr & Hnth_error).
    rewrite Hnth_error in H2.
    inversion H2.
    eapply nth_error_nth in Hnth_error.
    rewrite Hnth_error in Hmatch.
    subst.
    {
      unfold match_res, mr_correct, match_region.
      split.
      apply nth_In; lia.
      split; [| assumption].
      rewrite Ptrofs.add_zero_l.
      eexists.
      split; [reflexivity |].
      simpl.
      unfold Ctypes.align_attr; simpl.
      unfold Z.max, align; simpl.
      unfold Ptrofs.of_intu, Ptrofs.of_int.
      unfold Ptrofs.mul.
      change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16%Z.
      rewrite Hmrs_num_eq in Hrange.
      change Ptrofs.max_unsigned with Int.max_unsigned in Hrange.
      assert (HrangeZ_of_Nat: (0 <= Z.of_nat c < Int.max_unsigned)%Z) by lia.
      rewrite Int.unsigned_repr; [| lia].
      change Int.max_unsigned with Ptrofs.max_unsigned in HrangeZ_of_Nat.
      rewrite Ptrofs.unsigned_repr; [| lia].
      assumption.
    }
    - constructor.
Qed.

End Get_mem_region.

Existing Instance correct_function_get_mem_region.
