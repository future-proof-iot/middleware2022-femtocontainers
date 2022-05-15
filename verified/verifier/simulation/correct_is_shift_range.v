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

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.


(**
Check is_shift_range.
is_shift_range
     : int64 -> M bool
*)

Section Is_shift_range.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type); (int:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := is_shift_range.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_is_shift_range.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (int64_correct x))
        (dcons (fun x => StateLess _ (uint32_correct x))
          (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x  => StateLess _ (bool_correct x).

  Instance correct_function_is_shift_range : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f. unfold is_shift_range.
    correct_forward.

    get_invariant _i.
    get_invariant _upper.
    unfold eval_inv, int64_correct in c1.
    unfold eval_inv, uint32_correct in c2.
    destruct c2 as (c2 & c2_range).
    subst.

    eexists.

    split_and; auto.
    {
      unfold exec_expr. repeat
      match goal with
      | H: ?X = _ |- context [match ?X with _ => _ end] =>
        rewrite H
      end. simpl.
      unfold Cop.sem_shr, Cop.sem_shift; simpl.
      change Int64.iwordsize with (Int64.repr 64).
      change (Int64.ltu (Int64.repr 32) (Int64.repr 64)) with true; simpl.
      unfold Cop.sem_cmp; simpl.
      unfold Cop.sem_binarith; simpl.
      unfold Val.of_bool; simpl.
      unfold Vtrue, Vfalse.
      reflexivity.
    }

    unfold eval_inv, match_res, state.is_shift_range', typeof.
    unfold bool_correct, Val.of_bool, BinrBPF.get_immediate.
    unfold Int.cmpu, rBPFValues.int64_to_sint32.
    match goal with
    | |- (if ?X then _ else _) = _ =>
      destruct X; reflexivity
    end.
    unfold Cop.sem_cast; simpl.
    match goal with
    | |- context[if ?X then _ else _] =>
      destruct X; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity
    end.
    intros.
    match goal with
    | |- context[if ?X then _ else _] =>
      destruct X; constructor; reflexivity
    end.
  Qed.

End Is_shift_range.

Existing  Instance correct_function_is_shift_range.
