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

From bpf.comm Require Import MemRegion State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.

From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.clightlogic Require Import clight_exec Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_eval_mrs_regions correct_get_mem_region correct_upd_reg correct_bpf_interpreter_aux correct_eval_flag correct_eval_reg.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check bpf_interpreter.
bpf_interpreter
     : nat -> M val
*)

Section Bpf_interpreter.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := bpf_interpreter.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_interpreter.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list :DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
      (dcons (stateless nat_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x => StateLess _ (val64_correct x).

  Instance correct_function_bpf_interpreter : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app.
    unfold bpf_interpreter.
    correct_forward.

    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    intuition eauto.
    intros.

    correct_forward.

    get_invariant _mrs.
    exists ((Vint (Int.repr 0))::v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold correct_eval_mrs_regions.match_res in c0.
    unfold stateless, nat_correct.
    intuition eauto.
    change Int.max_unsigned with 4294967295%Z.
    lia.
    intros.


    eapply correct_statement_seq_body with (modifies2:=ModSomething).
    change_app_for_statement.
    eapply correct_statement_call with (has_cast := false).
    my_reflex.
    reflexivity.
    reflexivity.
    apply correct_function_strengthen.
    typeclasses eauto.

    reflexivity.
    reflexivity.
    reflexivity.
    prove_in_inv.
    prove_in_inv.
    reflexivity.
    reflexivity.

    intros H; correct_Forall.
    get_invariant _bpf_ctx.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold eval_inv, correct_get_mem_region.match_res, mr_correct in c0.
    intuition eauto.
    intros.

    correct_forward.

    get_invariant _st.
    get_invariant _start.
    unfold correct_get_start_addr.match_res, val32_correct in c1.
    destruct c1 as (c1 & vi & Hvi_eq).
    subst.
    exists (v::(Vint (Int.repr 1))::(Vlong (Int64.repr (Int.unsigned vi)))::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p1.
    simpl.
    reflexivity.
    intros; simpl.
    unfold val64_correct, stateless, reg_correct.
    intuition eauto.
    intros.

    correct_forward.

    get_invariant _st.
    get_invariant _fuel.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
    intros; simpl.
    intuition eauto.
    intros.

    correct_forward.

    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    intuition eauto.
    intros.

    correct_forward.
    {
      correct_forward.

      get_invariant _st.
      exists (v:: (Vint (Int.repr 0))::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0; reflexivity.
      intros; simpl.
      unfold stateless, reg_correct.
      intuition eauto.
      intros.

      correct_forward.

      get_invariant _res.
      unfold eval_inv, correct_eval_reg.match_res, val64_correct in c0.
      destruct c0 as (c0 & vl & Hvl_eq); subst.
      exists (Vlong vl).
      split.
      unfold exec_expr. rewrite p0. reflexivity.

      split.
      unfold eval_inv, match_res, val64_correct.
      intuition eauto.
      split.
      reflexivity.
      intros.
      constructor.
    }

    correct_forward; eauto.
    eexists.
    split.
    unfold exec_expr; simpl.
    reflexivity.
    split.
    unfold match_res, val64_correct, Int64.zero; simpl.
    intuition eauto.
    split.
    reflexivity.
    intros.
    constructor.
    all: try reflexivity.

    get_invariant _f.
    unfold exec_expr.
    unfold eval_inv, correct_eval_flag.match_res, flag_correct in c0.
    rewrite p0.
    rewrite c0.
    unfold Val.of_bool, CommonLib.int_of_flag, CommonLib.Z_of_flag.
    destruct x4; reflexivity.
Qed.

End Bpf_interpreter.

Existing Instance correct_function_bpf_interpreter.
