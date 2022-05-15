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

From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Flag Regs State Monad rBPFAST rBPFValues rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values AST Clight Memory Memtype Integers.

From bpf.clight Require Import interpreter.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import correct_upd_flag correct_eval_ins_len correct_eval_pc correct_eval_flag correct_step correct_upd_pc_incr.

From bpf.simulation Require Import MatchState InterpreterRel.

Open Scope Z_scope.


(**
Check bpf_interpreter_aux.
bpf_interpreter_aux
     : nat -> M unit
*)

Section Bpf_interpreter_aux.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := bpf_interpreter_aux.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_interpreter_aux.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list :DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
      (dcons (stateless nat_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x => StateLess _ (eq Vundef).

Lemma bpf_interpreter_aux_eq: forall n,
  bpf_interpreter_aux n =
    if Nat.eqb n 0 then bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt)
    else
        bindM eval_ins_len (fun len => 
          (bindM eval_pc (fun pc =>
            if (Int.ltu pc len) then
            (bindM rBPFInterpreter.step (fun _ =>
              (bindM eval_flag (fun f =>
                if flag_eq f BPF_OK then
                  bindM eval_ins_len (fun len0 => 
                    (bindM eval_pc (fun pc0 =>
                    if (Int.ltu (Int.add pc0 Int.one) len0) then
                      (bindM upd_pc_incr (fun _ =>
                        bpf_interpreter_aux (Nat.pred n)))
                    else
                      bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt))))
                else
                  returnM tt))))
            else
              bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt)))).
Proof.
  destruct n.
  - simpl. intros; reflexivity.
  - intros.
    simpl.
    reflexivity.
Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma mod_eq : forall (x y:Z), (x >= 0 -> y > 0 -> x mod y = x -> x < y)%Z.
Proof.
  intros.
  zify.
  intuition subst ; try lia.
Qed.

  Instance correct_function_bpf_interpreter_aux : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    intros.
    unfold args in a.
    car_cdr.
    induction c.
    {
      intros.
      correct_function_from_body args.
      unfold f. unfold cl_app. intros. rewrite bpf_interpreter_aux_eq.
      remember (0 =? 0)%nat as cmp.
      simpl.
      rewrite Heqcmp.
      correct_forward.
      correct_forward.

      get_invariant _st.
      exists (v ::
              (Vint (Int.neg (Int.repr 5))) :: nil). (**r star here *)
      unfold map_opt, exec_expr.
      rewrite p0.
      unfold Cop.sem_unary_operation; simpl.
      split.
      reflexivity.
      intros.
      unfold stateless, flag_correct, CommonLib.int_of_flag; simpl.
      intuition congruence.
      intros.

      (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
      correct_forward.
      unfold match_res, correct_get_opcode_alu64.match_res.

      unfold eval_inv; auto.

      inversion Hcnd.

      get_invariant _fuel.
      unfold exec_expr.
      rewrite p0.
      unfold stateless, nat_correct in c.
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
    rewrite bpf_interpreter_aux_eq.
    correct_forward.
    inversion Hcnd.
    simpl.
    apply correct_statement_seq_set with (match_res1 := stateless nat_correct c).

    intros Hst H; simpl in H.
    get_invariant _fuel.
    unfold eval_inv, stateless, nat_correct in c0.
    destruct c0 as (c0 & Hc0_range).
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
      unfold eval_inv, stateless, nat_correct.
      split. reflexivity. lia.
    }
    constructor.
    simpl.
    reflexivity.
    prove_in_inv.

    intros.
    (**r correct_body _ _ (bindM (eval_ins_len _ _) ... *)
    correct_forward.

    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    intuition eauto.
    intros.

    (**r correct_body _ _ (bindM (eval_pc _ _) ... *)
    correct_forward.

    get_invariant _st.
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

      get_invariant _st.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      intuition eauto.
      intros.

      correct_forward.

      get_invariant _st.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      intuition eauto.
      intros.

      correct_forward.
      {
        - (**r correct_body _ _ (bindM (eval_ins_len _ _) ... *)
          correct_forward.

          get_invariant _st.
          exists (v::nil).
          split.
          unfold map_opt, exec_expr.
          rewrite p0; reflexivity.
          simpl;intros.
          intuition eauto.
          intros.

          (**r correct_body _ _ (bindM (eval_pc _ _) ... *)
          correct_forward.

          get_invariant _st.
          exists (v::nil).
          split.
          unfold map_opt, exec_expr.
          rewrite p0; reflexivity.
          simpl;intros.
          intuition eauto.
          intros.

          correct_forward.
          + correct_forward.

            get_invariant _st.
            exists (v::nil).
            split.
            unfold map_opt, exec_expr.
            rewrite p0; reflexivity.
            simpl;intros.
            intuition eauto.
            intros.

          assert (Heq: bpf_interpreter_aux c = bindM (bpf_interpreter_aux c) (fun _ : unit => returnM tt)). {
            clear.
            unfold bindM, returnM.
            induction c.
            simpl. unfold upd_flag; reflexivity.
            simpl.
            unfold bpf_interpreter_aux.
            unfold bindM.
            apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intro.
            destruct eval_ins_len; [| reflexivity].
            destruct p0.
            destruct eval_pc; [| reflexivity].
            destruct p0.
            destruct Int.ltu; [| reflexivity].
            destruct rBPFInterpreter.step; [| reflexivity].
            destruct p0.
            destruct eval_flag; [| reflexivity].
            destruct p0.
            destruct flag_eq; [| reflexivity].
            destruct eval_ins_len; [| reflexivity].
            destruct p0.
            destruct eval_pc; [| reflexivity].
            destruct p0.
            destruct Int.ltu; [| reflexivity].
            destruct upd_pc_incr; [| reflexivity].
            destruct p0.
            unfold bpf_interpreter_aux in IHc.
            unfold bindM in IHc.
            rewrite IHc.

            destruct (fix bpf_interpreter_aux (fuel : nat) : M _ unit :=
         match fuel with
         | 0%nat => upd_flag BPF_ILLEGAL_LEN
         | Datatypes.S fuel0 =>
             fun st : State.state =>
             match eval_ins_len st with
             | Some (x', st') =>
                 match eval_pc st' with
                 | Some (x'0, st'0) =>
                     (if Int.ltu x'0 x'
                      then
                       fun st0 : State.state =>
                       match rBPFInterpreter.step st0 with
                       | Some (_, st'1) =>
                           match eval_flag st'1 with
                           | Some (x'2, st'2) =>
                               (if flag_eq x'2 BPF_OK
                                then
                                 fun st1 : State.state =>
                                 match eval_ins_len st1 with
                                 | Some (x'3, st'3) =>
                                     match eval_pc st'3 with
                                     | Some (x'4, st'4) =>
                                         (if Int.ltu (Int.add x'4 Int.one) x'3
                                          then
                                           fun st2 : State.state =>
                                           match upd_pc_incr st2 with
                                           | Some (_, st'5) =>
                                               bpf_interpreter_aux fuel0 st'5
                                           | None => None
                                           end
                                          else upd_flag BPF_ILLEGAL_LEN) st'4
                                     | None => None
                                     end
                                 | None => None
                                 end
                                else returnM tt) st'2
                           | None => None
                           end
                       | None => None
                       end
                      else upd_flag BPF_ILLEGAL_LEN) st'0
                 | None => None
                 end
             | None => None
             end
         end); try reflexivity.
            destruct p0.
            auto.
            }
            rewrite Heq; clear Heq.
            correct_forward.

            get_invariant _st.
            get_invariant _fuel0.
            exists (v::v0::nil).
            split.
            unfold map_opt, exec_expr.
            rewrite p0, p1; reflexivity.
            intros; simpl.
            intuition eauto.

            intros.
            correct_forward.
            unfold eval_inv.
            unfold match_res.
            reflexivity.
          + correct_forward.

            get_invariant _st.
            exists (v::(Vint (Int.neg (Int.repr 5))) :: nil).
            split.
            unfold map_opt, exec_expr.
            rewrite p0; reflexivity.
            simpl;intros.
            unfold stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
            intuition eauto.
            intros.

            correct_forward.
            unfold eval_inv.
            unfold match_res.
            reflexivity.
          + get_invariant _pc0.
            get_invariant _len0.
            unfold exec_expr. rewrite p0, p1.
            unfold eval_inv, correct_eval_pc.match_res, uint32_correct in c0.
            destruct c0 as (c0 & c0_range).
            unfold eval_inv, correct_eval_ins_len.match_res, uint32_correct in c1.
            destruct c1 as (c1 & c10_range).
            subst.
            simpl.
            unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
            reflexivity.
      }

      correct_forward.

      unfold eval_inv.
      unfold match_res.
      reflexivity.

      get_invariant _f.
      unfold exec_expr.
      rewrite p0.
      unfold eval_inv, correct_eval_flag.match_res, flag_correct in c0.
      rewrite c0.
      unfold Cop.sem_binary_operation.
      unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
      unfold flag_eq, CommonLib.int_of_flag.
      unfold Val.of_bool, Vtrue, Vfalse.
      destruct x2 eqn: Heq_x2; simpl; try reflexivity.
    }

    correct_forward.

    get_invariant _st.
    exists (v::(Vint (Int.neg (Int.repr 5))) :: nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    unfold stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
    intuition eauto.
    intros.

    correct_forward.

    unfold eval_inv.
    unfold match_res.
    reflexivity.

    get_invariant _pc.
    get_invariant _len.
    unfold exec_expr. rewrite p0, p1.
    unfold eval_inv, correct_eval_pc.match_res, uint32_correct in c0.
    destruct c0 as (c0 & c0_range).
    unfold eval_inv, correct_eval_ins_len.match_res, uint32_correct in c1.
    destruct c1 as (c1 & c10_range).
    subst.
    simpl.
    unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
    reflexivity.

    get_invariant _fuel.
    unfold stateless, nat_correct in c0.
    destruct c0 as (Hv_eq & Hrange).
    unfold exec_expr.
    rewrite p0.
    simpl.
    rewrite <- Hv_eq.
    unfold Cop.sem_cmp, Cop.sem_binarith, Val.of_bool, Vfalse; simpl.
    unfold Int.eq.
    change (Int.unsigned (Int.repr 0)) with 0.
    rewrite Int.unsigned_repr;[ | lia].
    assert (Hneq: (Z.succ (Z.of_nat c)) <> 0). {
      lia.
    }
    eapply zeq_false with (a:= true) (b:= false) in Hneq.
    rewrite Zpos_P_of_succ_nat.
    rewrite Hneq.
    reflexivity.
Qed.

End Bpf_interpreter_aux.

Close Scope Z_scope.

Existing Instance correct_function_bpf_interpreter_aux.
