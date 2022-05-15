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

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.
From bpf.verifier.simulation Require Import correct_bpf_verifier_eval_ins  correct_is_well_dst correct_bpf_verifier_get_opcode correct_bpf_verifier_aux2.


(**
Check bpf_verifier_aux.
bpf_verifier_aux
     : nat -> nat -> M state.state bool

*)
Open Scope Z_scope.

Section Bpf_verifier_aux.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (nat:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_aux.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_aux.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun _ => StateLess _ is_state_handle)
      (dcons (fun x => StateLess _ (nat_correct x))
        (dcons (fun x => StateLess _ (nat_correct x))
          (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

Lemma bpf_verifier_aux_eq: forall n len,
  bpf_verifier_aux n len =
    if Nat.eqb n 0 then (returnM true)
    else
      bindM (eval_ins (Int.repr (Z.of_nat (Nat.pred n))))
      (fun ins : int64 =>
       bindM (is_well_dst ins)
         (fun b : bool =>
          if b
          then
           bindM (get_opcode ins)
             (fun op : nat =>
              bindM (bpf_verifier_aux2 (Nat.pred n) len op ins)
                (fun b0 : bool =>
                 if b0 then bpf_verifier_aux (Nat.pred n) len else returnM false))
          else returnM false)).
Proof.
  destruct n; intros.
  - simpl. reflexivity.
  - simpl.
    reflexivity.
Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma mod_eq : forall (x y:Z), (x >= 0 -> y > 0 -> x mod y = x -> x < y)%Z.
Proof.
  intros.
  zify.
  intuition subst ; try lia.
Qed.

  Instance correct_function_bpf_verifier_aux : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    intros.
    unfold args in a.
    car_cdr.
    induction c.
    {
      correct_function_from_body args.
      unfold f. unfold cl_app. intros. rewrite bpf_verifier_aux_eq.
      remember (0 =? 0)%nat as cmp.
      simpl.
      rewrite Heqcmp.

      correct_forward.
      correct_forward.

      exists (Vint (Int.repr 1)).
      unfold exec_expr, eval_inv.
      split; [reflexivity |].
      unfold bool_correct; simpl.
      fold Int.one.
      split; [reflexivity |].
      unfold Cop.sem_cast; simpl.
      rewrite Int_eq_one_zero.
      split; [reflexivity |].
      intros.
      constructor.
      reflexivity.

      inversion Hcnd.

      get_invariant _pc.
      unfold exec_expr.
      rewrite p0.
      unfold eval_inv, opcode_correct in c.
      destruct c as (c & _).
      rewrite <- c.
      unfold Cop.sem_binary_operation, typeof; simpl.
      unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
      unfold Val.of_bool.
      rewrite Int.eq_true.
      reflexivity.
    }

    intros.
    correct_function_from_body args.
    correct_body.
    unfold f, cl_app.
    rewrite bpf_verifier_aux_eq.

    correct_forward.
    inversion Hcnd.
    simpl.
    apply correct_statement_seq_set with (match_res1 := StateLess state.state (nat_correct c)).

    intro Hst.
    unfold INV; intro H.
    get_invariant _pc.
    unfold eval_inv, nat_correct in c1.
    destruct c1 as (c1 & Hc1_range).
    subst.
    eexists.
    split.
    {
      unfold exec_expr.
      rewrite p0.
      unfold Cop.sem_binary_operation, Cop.sem_sub; simpl.
      unfold Cop.sem_binarith; simpl.
      unfold Int.sub.
      fold Int.one; rewrite Int.unsigned_one.
      rewrite Zpos_P_of_succ_nat.
      rewrite <- Nat2Z.inj_succ.
      rewrite Int.unsigned_repr; [ | lia].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      rewrite Z.add_simpl_r.
      reflexivity.
    }
    split.
    {
      unfold eval_inv, nat_correct.
      split; [reflexivity | lia].
    }
    constructor.
    simpl.
    reflexivity.
    prove_in_inv.

    intros.
    correct_forward.

    get_invariant _st.
    get_invariant _n.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1; reflexivity.
    simpl;intros.
    intuition eauto.
    unfold uint32_correct.
    unfold eval_inv, nat_correct in c2.
    destruct c2 as (c2 & c2_range).
    split; [assumption |].
    rewrite Int.unsigned_repr; lia.
    intros.

    correct_forward.

    get_invariant _ins.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    intuition eauto.
    intros.

    correct_forward.
    {
      correct_forward.

      get_invariant _ins.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      intuition eauto.
      intros.

      correct_forward.

      get_invariant _n.
      get_invariant _len.
      get_invariant _op.
      get_invariant _ins.
      exists (v::v0::v1::v2::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0,p1,p2,p3; reflexivity.
      simpl;intros.
      intuition eauto.
      intros.

      correct_forward.
      {
        change_app_for_body.
        eapply correct_body_call_ret with (has_cast:=false).

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall; simpl in H.
        get_invariant _st.
        get_invariant _n.
        get_invariant _len.
        exists (v :: v0 :: v1 :: nil).
        split.
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2; reflexivity.
        simpl;intros.
        intuition eauto.
      }

      { correct_forward.
        exists (Vint (Int.repr 0)); split_and.
        -
          unfold exec_expr. reflexivity.
        -
          unfold eval_inv, match_res, bool_correct, Int.zero.
          reflexivity.
        - simpl.
          unfold Cop.sem_cast; simpl.
          fold Int.zero; rewrite Int.eq_true; reflexivity.
        - intros.
          constructor.
          reflexivity.
      }

      get_invariant _b0.
      unfold map_opt, exec_expr.
      rewrite p0.
      unfold eval_inv, correct_bpf_verifier_aux2.match_res, bool_correct in c1.
      rewrite c1.
      destruct x2; reflexivity.
    }
    { correct_forward.
      exists (Vint (Int.repr 0)); split_and.
      -
        unfold exec_expr. reflexivity.
      -
        unfold eval_inv, match_res, bool_correct, Int.zero.
        reflexivity.
      - simpl.
        unfold Cop.sem_cast; simpl.
        fold Int.zero; rewrite Int.eq_true; reflexivity.
      - intros.
        constructor.
        reflexivity.
    }

    get_invariant _b.
    unfold map_opt, exec_expr.
    rewrite p0.
    unfold eval_inv, correct_is_well_dst.match_res, bool_correct in c1.
    rewrite c1.
    destruct x0; reflexivity.

    get_invariant _pc.
    unfold map_opt, exec_expr.
    rewrite p0.
    unfold eval_inv, nat_correct in c1.
    destruct c1 as (c1 & Hc1_range).
    rewrite <- c1.
    unfold Cop.sem_binary_operation; simpl.
    unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
    unfold Val.of_bool, Vfalse.
    unfold Int.eq.
    change (Int.unsigned (Int.repr 0)) with 0.
    rewrite Int.unsigned_repr;[ | lia].
    assert (Hneq: (Z.succ (Z.of_nat c)) <> 0). {
      lia.
    }
    eapply Coqlib.zeq_false with (a:= true) (b:= false) in Hneq.
    rewrite Zpos_P_of_succ_nat.
    rewrite Hneq.
    reflexivity.
Qed.

End Bpf_verifier_aux.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_aux.
