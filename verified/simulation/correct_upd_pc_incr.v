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
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check upd_pc_incr.
upd_pc_incr
     : M unit
 *)

Section Upd_pc_incr.
  Context{S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := upd_pc_incr.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_pc_incr.

  Definition modifies  := ModSomething. (* of the C code *)
  (* [match_mem] related the Coq monadic state and the C memory *)
  (*Definition match_mem : stateM -> val -> Memory.Mem.mem -> Prop := fun stM v m => match_meminj_state state_block inject_id stM m.*)


  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons  (fun (x:unit) => StateLess _ (is_state_handle))
                             (DList.DNil _).


  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun _  => StateLess _ (fun v => v = Vundef).

  Lemma correct_function_upd_pc_incr : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold f; simpl.
    destruct upd_pc_incr eqn: Hupd_pc; [| constructor].
    destruct p0.
    intros.
    unfold INV in H.
    get_invariant _st. unfold eval_inv,is_state_handle in c. subst.

    (** we need to get the proof of `upd_pc_incr` load/store permission *)
    apply (upd_pc_store  _ (Int.add (pc_loc st) (Int.repr 1)) _) in MS as Hstore.
    destruct Hstore as (m1 & Hstore).
    (** pc \in [ (state_block,0), (state_block,8) ) *)

    (**according to the type of upd_pc_incr:
         static void upd_pc_incr(struct bpf_state* st) 
       1. return value should be Vundef (i.e. void)
       2. the new memory should change the value of pc, i.e. m_pc
      *)
    exists Vundef, m1, Events.E0.

    split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.

      rewrite Ptrofs.add_zero.
      destruct MS as (_ , Hpc, _, _, _, _, _, _, _, _).
      fold Ptrofs.zero in Hpc.
      rewrite Hpc; reflexivity.
      reflexivity.
      reflexivity.
    - split_and; auto.
      constructor.
      eapply upd_pc_preserves_match_state; eauto.
      unfold upd_pc_incr in Hupd_pc.
      context_destruct_if_inversion.
      unfold State.upd_pc, State.upd_pc_incr.
      reflexivity.
Qed.

End Upd_pc_incr.

Existing Instance correct_function_upd_pc_incr.
