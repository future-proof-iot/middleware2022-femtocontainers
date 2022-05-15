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

From bpf.comm Require Import Regs BinrBPF State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check get_dst.
get_dst
     : int64_t -> M reg

 *)

Open Scope Z_scope.

Section Get_dst.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (reg:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_dst.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_dst.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (int64_correct x))
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x => StateLess _ (reg_correct x).

  Instance correct_function_get_dst : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    simpl.
    unfold get_dst, int64_to_dst_reg.
    destruct int64_to_dst_reg' eqn: Hdst; [| constructor].
    unfold int64_to_dst_reg' in Hdst.

    get_invariant _ins.

    unfold eval_inv, int64_correct in c0.
    subst.

    (**according to the type:
         static unsigned int get_dst(unsigned long long ins1)
       1. return value should be  
       2. the memory is same
     *)
    unfold z_to_reg, BinrBPF.get_dst in Hdst.
    simpl in c.
    exists (Vint (Int.repr (Int64.unsigned (Int64.shru (Int64.and c (Int64.repr 4095)) (Int64.repr 8))))), m, Events.E0.

    split_and; unfold step2;auto.
    -
      repeat forward_star.
    -
      unfold match_res.
      unfold reg_correct. (**r we need the invariant reg \in [0; 10] *)
      remember ((Int64.unsigned (Int64.shru (Int64.and c (Int64.repr 4095)) (Int64.repr 8)))) as X.
      Ltac zeqb :=
      match goal with
      | |- context[?X1 =? ?X2] =>
          destruct (Z.eqb X1 X2) eqn:Heq; [
      rewrite Z.eqb_eq in Heq; rewrite Heq; try reflexivity | rewrite Z.eqb_neq in Heq]
      end.
      destruct (X =? 0) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq0].

      destruct (X =? 1) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq1].

      destruct (X =? 2) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq2].

      destruct (X =? 3) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq3].

      destruct (X =? 4) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq4].

      destruct (X =? 5) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq5].

      destruct (X =? 6) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq6].

      destruct (X =? 7) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq7].

      destruct (X =? 8) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq8].

      destruct (X =? 9) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq9].

      destruct (X =? 10) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hdst; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq10].

      inversion Hdst.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Get_dst.
Close Scope Z_scope.

Existing Instance correct_function_get_dst.
