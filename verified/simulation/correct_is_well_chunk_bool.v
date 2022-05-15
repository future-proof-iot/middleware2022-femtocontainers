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

From bpf.comm Require Import rBPFAST State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.clightlogic Require Import clight_exec Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.

Section Is_well_chunk_bool.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [memory_chunk:Type].
  Definition res : Type := bool.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f := is_well_chunk_bool.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_is_well_chunk_bool.


  Ltac exec_seq_of_labeled_statement :=
    match goal with
    | |- context[seq_of_labeled_statement ?X] =>
        let x := (eval simpl in (seq_of_labeled_statement X)) in
        change (seq_of_labeled_statement X) with x
    end.

  Instance correct_function_is_well_chunk_bool2 : forall a, correct_function _
      p args res f fn ModNothing true match_state (dcons  (stateless match_chunk) (DList.DNil _)) (stateless match_bool) a.
  Proof.
    correct_function_from_body args.
    correct_body.
    unfold INV, f.
    repeat intro.
    simpl in *.
    destruct (is_well_chunk_bool c st) eqn: Heq; [idtac | constructor].
    destruct p0 as (v',st'); intros.

    get_invariant _chunk.
    unfold stateless, eval_inv, match_chunk in c0.
    subst.

    exists (Vint (if v' then Integers.Int.one else Integers.Int.zero)).
    exists m, Events.E0.
    
    split_and; unfold step2;auto.
    -
      unfold memory_chunk_to_valu32, well_chunk_Z in p0.
      unfold align_chunk in p0.
      destruct c; inv Heq; simpl.
      all: try
      forward_star; forward_star;
      [ rewrite Int.unsigned_repr; [idtac | rewrite Int_max_unsigned_eq64; lia]; simpl; forward_star |
      repeat forward_star | reflexivity].
    - unfold match_bool. reflexivity.
    - constructor. destruct v'.
      reflexivity. reflexivity.
    - unfold is_well_chunk_bool in Heq.
      destruct c; inv Heq;auto.
    - unfold is_well_chunk_bool in Heq.
      destruct c; inv Heq;auto.
  Qed.

End Is_well_chunk_bool.

Existing Instance correct_function_is_well_chunk_bool2.
