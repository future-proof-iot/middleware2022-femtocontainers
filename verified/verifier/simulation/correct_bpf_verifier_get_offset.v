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

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.


(**
Check get_offset.
get_offset
     : int64 -> M int

 *)

Open Scope Z_scope.

Section Get_offset.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (int:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := get_offset.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_offset.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (int64_correct x))
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x  => StateLess _ (sint32_correct x).

  Instance correct_function_bpf_verifier_get_offset : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f. unfold get_offset.
    correct_forward.

    get_invariant _i.

    unfold eval_inv, int64_correct in c0.
    subst.

    eexists.

    split_and; auto.
    {
      unfold exec_expr. repeat
      match goal with
      | H: ?X = _ |- context [match ?X with _ => _ end] =>
        rewrite H
      end. simpl.
      unfold Cop.sem_shl, Cop.sem_shift; simpl.
      change Int64.iwordsize with (Int64.repr 64).
      change (Int64.ltu (Int64.repr 32) (Int64.repr 64)) with true; simpl.
      unfold Cop.sem_shr; simpl.
      unfold Cop.sem_shift; simpl.
      change Int64.iwordsize with (Int64.repr 64).
      change (Int64.ltu (Int64.repr 48) (Int64.repr 64)) with true; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
    }
    {
      unfold match_res, sint32_correct, BinrBPF.get_offset; simpl.
      split; [reflexivity | apply Int.signed_range].
    }
    unfold Cop.sem_cast; simpl.
    reflexivity.
  Qed.

End Get_offset.
Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_get_offset.
