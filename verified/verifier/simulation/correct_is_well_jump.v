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
Check is_well_jump.
is_well_jump
     : int64 -> M bool
*)

Section Is_well_jump.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (nat:Type); (int:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := is_well_jump.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_is_well_jump.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (nat_correct x))
      (dcons (fun x => StateLess _ (nat_correct x))
        (dcons (fun x => StateLess _ (sint32_correct x))
          (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_is_well_jump : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f. unfold is_well_jump.
    correct_forward.

    get_invariant _pc.
    get_invariant _len.
    get_invariant _ofs.
    unfold eval_inv, nat_correct in c2, c3.
    unfold eval_inv, sint32_correct in c4.
    destruct c2 as (c2 & Hc2_range).
    destruct c3 as (c3 & Hc3_range).
    destruct c4 as (c4 & Hc4_range).
    subst.

    eexists.

    split_and; auto.
    {
      unfold exec_expr. repeat
      match goal with
      | H: ?X = _ |- context [match ?X with _ => _ end] =>
        rewrite H
      end. simpl.
      unfold Cop.sem_cmp; simpl.
      unfold Cop.sem_binarith; simpl.
      unfold Val.of_bool; simpl.
      unfold Vtrue, Vfalse.
      reflexivity.
    }
    unfold eval_inv, match_res, state.is_well_jump'.
    unfold bool_correct, Val.of_bool.
    unfold Int.cmpu.
    match goal with
    | |- context[if ?X then _ else _] =>
      destruct X; reflexivity
    end.
    unfold Cop.sem_cast; simpl.
    match goal with
    | |- context[if ?X then _ else _] =>
      destruct X; reflexivity
    end.
    intros.
    match goal with
    | |- Cop.val_casted (if ?X then _ else _) _ =>
      destruct X; constructor; reflexivity
    end.
  Qed.

End Is_well_jump.

Existing  Instance correct_function_is_well_jump.
