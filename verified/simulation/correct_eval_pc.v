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

From bpf.comm Require Import State Monad rBPFMonadOp.
From Coq Require Import List Lia ZArith.
From compcert Require Import Coqlib Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check eval_pc.
eval_pc
     : M sint32_t
*)

Section Eval_pc.
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (int:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := eval_pc.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_pc.

Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
  dcons
    (fun x => StateLess _ is_state_handle)
    (DList.DNil _).


  (* [match_res] relates the Coq result and the C result *)

Definition match_res : res -> Inv State.state := fun x  => StateLess _ (uint32_correct x).

Instance correct_function_eval_pc :
  forall a, correct_function _ p args res f fn ModNothing false (match_state ) match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    eapply correct_body_Sreturn_Some.
    repeat intro.
    unfold INV in H0.
    get_invariant _st.
    exists (Vint (pc_loc st)).
    split_and.
    -
    unfold exec_expr.
    unfold eval_inv in c. unfold is_state_handle in c.
    subst. rewrite p0.
    simpl. unfold exec_deref_loc.
    simpl.
    inv H.
    unfold Coqlib.align; rewrite Ptrofs.add_zero.
    unfold Ptrofs.zero; simpl.
    rewrite Ptrofs.unsigned_repr.
    rewrite <- mpc; reflexivity.
    rewrite Ptrofs_max_unsigned_eq32.
    lia.
    - simpl.
      unfold uint32_correct.
      unfold State.eval_pc.
      split.
      constructor.
      apply Int.unsigned_range_2.
    - simpl. reflexivity.
    - simpl ; auto.
  Qed.

End Eval_pc.

Existing  Instance correct_function_eval_pc.
