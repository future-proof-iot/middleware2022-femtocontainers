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

From bpf.comm Require Import MemRegion State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.clightlogic Require Import clight_exec Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_is_well_chunk_bool correct_eval_mrs_num correct_eval_mrs_regions correct_check_mem_aux correct_cmp_ptr32_nullM.

From bpf.simulation Require Import MatchState InterpreterRel.

(**
Check check_mem.
check_mem
     : permission -> memory_chunk -> val -> M val
*)

Section Check_mem.
  Context {S:special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(permission:Type); (memory_chunk:Type); (val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := check_mem.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_check_mem.


  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun _ => StateLess _ is_state_handle)
      (dcons (stateless perm_correct)
        (dcons (stateless match_chunk)
          (dcons (stateless val32_correct)
            (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state:= stateless eq.

  Instance correct_function_check_mem : forall a, correct_function _ p args res f fn ModNothing  false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, cl_app.
    unfold check_mem.
    correct_forward.

    get_invariant _chunk.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0.
    reflexivity.
    intros; simpl.
    intuition eauto.

    intros.
    correct_forward.
    2:{ (**r if-else branch *)
        correct_forward.

        eexists ; split_and.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - simpl ; auto.
          intro. constructor. reflexivity.
    }
    (**r if-then branch *)

    correct_forward.

    get_invariant _st.
    unfold eval_inv in *.
    exists (v::nil).
    split_and.
    unfold map_opt,exec_expr.
    rewrite p0; reflexivity.
    simpl; intros.
    tauto.
      -
      intros.
      correct_forward.

      get_invariant _st.
      unfold eval_inv,stateless, is_state_handle in *.
      subst.
      exists (Vptr st_blk Ptrofs.zero::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      unfold is_state_handle. split ; auto.
      intros.
      correct_forward.

      get_invariant _st.
      get_invariant _mem_reg_num.
      get_invariant _perm.
      get_invariant _chunk.
      get_invariant _addr.
      get_invariant _mrs.
      exists (v :: v0 :: v1 :: v2 :: v3 :: v4 :: nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0, p1, p2, p3, p4, p5; reflexivity.
      simpl;intros.
      unfold correct_eval_mrs_num.match_res in c3.
      destruct c3 as (Hc_eq & _).
      unfold correct_eval_mrs_regions.match_res in c7.
      intuition eauto.

      intros.
      correct_forward.

      get_invariant _check_mem__1.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      unfold eval_inv,correct_check_mem_aux.match_res,stateless in c2.
      tauto.
      intros.

      correct_forward.
      2:{
          correct_forward.

          get_invariant _check_mem__1.
          exists v.
          split_and;auto.
          simpl.
          apply Cop.cast_val_casted;auto.
        }

      correct_forward.
      eexists.
      split_and.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      intro ; constructor; reflexivity.

      get_invariant _is_null.
      unfold exec_expr.
      unfold eval_inv,correct_cmp_ptr32_nullM.match_res, match_bool,stateless in c2.
      rewrite p0.
      rewrite c2.
      unfold Val.of_bool.
      destruct x3; reflexivity.
    - get_invariant _well_chunk.
      unfold exec_expr.
      rewrite p0.
      unfold eval_inv, stateless, match_bool in c2.
      unfold Val.of_bool.
      rewrite c2.
      destruct x; reflexivity.
  Qed.

End Check_mem.

Existing Instance correct_function_check_mem.
