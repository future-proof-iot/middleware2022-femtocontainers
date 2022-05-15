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

From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.


Section Eval_ins_len.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (nat:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := eval_ins_len.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_ins_len.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle) (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x  => StateLess _ (nat_correct x).

  Instance correct_function_bpf_verifier_eval_ins_len : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    unfold eval_inv, is_state_handle in c.
    subst.

    (** we need to get the value of pc in the memory *)
    assert (MS':=MS).
    destruct MS. clear - MS' p0 mins_len mins.
    destruct mins_len as (Hload_eq & Hge).

    eexists; exists m, Events.E0.

    split_and; auto.
    {
      forward_star.
      unfold Coqlib.align; rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.zero; simpl.
      unfold Mem.loadv in Hload_eq.
      apply Hload_eq.
      simpl.
      reflexivity.
      forward_star.
    }
    unfold state.eval_ins_len.
    unfold eval_inv, match_res, nat_correct.
    destruct mins as (_ & mins).
    unfold match_ins in mins.
    destruct mins as (Hlen & Hrange & _).
    rewrite Hlen in *.

    split;[reflexivity|].
    change Int.max_unsigned with Ptrofs.max_unsigned.
    lia.
    constructor. reflexivity.
    apply unmodifies_effect_refl.
  Qed.

End Eval_ins_len.

Existing  Instance correct_function_bpf_verifier_eval_ins_len.
