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

From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_immediate correct_eval_immediate correct_get_src correct_eval_reg.

From bpf.simulation Require Import MatchState InterpreterRel.

(**
Check get_src64.
get_src64
     : nat -> int64 -> M val

 *)

Open Scope Z_scope.

Section Get_src64.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_src64.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_src64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv State.state) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle)
      (dcons (fun x => StateLess _ (opcode_correct x))
        (dcons (fun x => StateLess _ (int64_correct x))
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => StateLess _ (val64_correct x).

  Instance correct_function_get_src64 : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, cl_app, get_src64.
    intros.

    correct_forward.
    - correct_forward.

      get_invariant _ins.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      intros; simpl. (**r TODO: need a verifier information ... *)
      tauto.

      intros.
      correct_forward.

      get_invariant _imm.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      intros; simpl.
      unfold correct_get_immediate.match_res in c1.
      tauto.
      intros.
      correct_forward.
      get_invariant _imm64.
      unfold correct_eval_immediate.match_res, val64_correct in c1.
      {
        destruct c1 as (Hv_eq & vl & Hvl_eq).
        subst.
        eexists.
        split_and.
        +
          unfold exec_expr, empty_env.
          rewrite p0. reflexivity.
        + unfold eval_inv. simpl.
          unfold val64_correct; simpl. eauto.
        + reflexivity.
        + simpl. auto.
      }
    - correct_forward.

      get_invariant _ins.
      exists (v::nil).
      split_and.
      { unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
      }
      { intros; simpl.
        unfold int64_correct.
        tauto.
      }
      intros.
      correct_forward.

      simpl in H.
      get_invariant _st.
      get_invariant _src.
      exists (v::v0::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0, p1.
      reflexivity.
      intros; simpl.
      unfold correct_get_src.match_res in c2.
      unfold eval_inv in *.
      tauto.

      intros.
      correct_forward.
      get_invariant _src64.
      unfold eval_inv, correct_eval_reg.match_res, val64_correct in c1.
      destruct c1 as (Hv_eq & vl & Hvl_eq).
      subst.
      eexists.
      split_and.
      { unfold exec_expr, empty_env.
        rewrite p0; reflexivity.
      }
      { unfold eval_inv. simpl.
        unfold val64_correct; simpl; eauto.
      }
      reflexivity.
      simpl; auto.
    - get_invariant _x.
      unfold exec_expr.
      rewrite p0.
      simpl.
      unfold eval_inv, opcode_correct in c1.
      destruct c1 as (Hv_eq & Hc_le); subst.
      unfold Cop.sem_and, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
      reflexivity.
  Qed.

End Get_src64.
Close Scope Z_scope.

Existing Instance correct_function_get_src64.
