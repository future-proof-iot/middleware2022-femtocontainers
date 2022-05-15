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
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clight Require Import interpreter.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check load_mem.

load_mem
     : memory_chunk -> valu32_t -> M val64_t

 *)

Section Load_mem.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_chunk:Type); val].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := load_mem.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_load_mem.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle)
          (dcons (fun ck => StateLess _ (match_chunk ck))
         (dcons (fun x => StateLess _ (eq x))
            (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x => StateLess _ (val64_correct x).

  Instance correct_function_load_mem : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, load_mem, State.load_mem, Mem.loadv, INV, app, _to_vlong.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  unfold eval_inv, is_state_handle in c1.
  unfold eval_inv, match_chunk in c2.
  unfold eval_inv in c3.
  subst.

  unfold rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z in p1.
  unfold match_res, val64_correct.

  assert (Hload_implies: forall v,
    Mem.loadv c (bpf_m st) v1 =  Some v -> Mem.loadv c m v1 = Some v). {
    unfold Mem.loadv.
    intros.
    destruct v1; try inversion H0.
    rewrite H2.
    eapply match_state_implies_loadv_equal; eauto.
  }
  destruct c, v1; try constructor.
  - (**r c = Mint8unsigned *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    all: intros; eexists; exists m, Events.E0.
    + (**r v = Vint i0 *)
      split_and.
      * forward_star.
      change (Int.unsigned (Int.repr 1)) with 1%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      rewrite <- Hv_eq in Hload.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
      * simpl. split_and; auto.
        eexists ; reflexivity.
      * constructor.
      * auto.
      * apply unmodifies_effect_refl.
    + (**r v = Vlong i0: it should be impossible *)
      apply Mem.load_type in Hload.
      inversion Hload.
  - (**r c = Mint16unsigned *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    all: intros; eexists; exists m, Events.E0.
    split_and; auto.
    + forward_star.
      change (Int.unsigned (Int.repr 2)) with 2%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      rewrite <- Hv_eq in Hload.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
    + simpl. split ; eauto.
    + constructor.
    + apply unmodifies_effect_refl.
    +  apply Mem.load_type in Hload.
      inversion Hload.
  - (**r c = Mint32 *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    all: intros; eexists; exists m, Events.E0.
    split_and; auto.
    + forward_star.
      change (Int.unsigned (Int.repr 4)) with 4%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      rewrite <- Hv_eq in Hload.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
    + simpl. split ; eauto.
    + constructor.
    + apply unmodifies_effect_refl.
    + apply Mem.load_type in Hload.
      inversion Hload.
  - (**r c = Mint64 *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq.
    constructor.
    all: rewrite <- Hv_eq in Hload.
    all: try (apply Mem.load_type in Hload as Hload1; rewrite Hv_eq in Hload1; inversion Hload1).
    all: intros; eexists; exists m, Events.E0.
    + split_and.
      * forward_star.
      change (Int.unsigned (Int.repr 8)) with 8%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
      * simpl. split ; eauto.
      * rewrite Hv_eq. constructor.
      * auto.
      * apply unmodifies_effect_refl.
      Unshelve.
      all: assumption.
Qed.

End Load_mem.

Existing Instance correct_function_load_mem.
