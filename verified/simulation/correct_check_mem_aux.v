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
From bpf.comm Require Import MemRegion Regs BinrBPF State Monad rBPFAST rBPFValues rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values AST Clight Memory Memtype Integers.

From bpf.clight Require Import interpreter.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import correct_check_mem_aux2 correct_get_mem_region correct_cmp_ptr32_nullM.

From bpf.simulation Require Import MatchState InterpreterRel.

Open Scope Z_scope.


(**
Check check_mem_aux.
check_mem_aux
     : nat ->
       permission -> AST.memory_chunk -> val -> MyMemRegionsType -> M val
*)

Section Check_mem_aux.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (permission:Type); (memory_chunk:Type); (val:Type); (list memory_region: Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := check_mem_aux.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_check_mem_aux.


  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle)
      (dcons (stateless nat_correct)
        (dcons (stateless perm_correct)
          (dcons (stateless match_chunk)
            (dcons (stateless val32_correct)
              (dcons (statefull (mrs_correct S))
                (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state:= stateless eq.

Lemma check_mem_aux_eq: forall n p c v l,
  check_mem_aux n p c v l =
    if Nat.eqb n 0 then returnM Vnullptr
    else bindM (get_mem_region (Nat.pred n) l) (fun cur_mr => 
          (bindM (check_mem_aux2 cur_mr p v c) (fun check_mem =>
            (bindM (cmp_ptr32_nullM check_mem) (fun is_null =>
              if is_null then check_mem_aux (Nat.pred n) p c v l
              else returnM check_mem))))).
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


  Instance correct_function_check_mem_aux : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    intros.
    unfold args in a.
    car_cdr.
    revert c c0 c1 c2 c3.
    induction c.
    {
      intros.
      correct_function_from_body args.
      correct_body.
      repeat intro.
      unfold INV in H.
      get_invariant _st.
      get_invariant _num.
      get_invariant _perm.
      get_invariant _chunk.
      get_invariant _addr.
      get_invariant _mrs.
      unfold stateless,statefull,eval_inv in *.
      unfold stateless in c4, c5, c6, c7.
      unfold nat_correct in c4.
      destruct c4 as (c4 & Hrange_mrs_num).
      unfold perm_correct in c5.
      unfold match_chunk, memory_chunk_to_valu32, well_chunk_Z in c6.
      unfold val32_correct in c7.
      destruct c7 as (Hv3_eq & (vi3 & Hc2_eq)).
      unfold mrs_correct, match_regions in c8.
      destruct c8 as (Hv4_eq & Hmrs_eq & (Hmrs_num_eq & Hrange & Hmatch) & _).
      subst.

      eexists; exists m, Events.E0.
      split_and;auto.
      {
        repeat forward_star.
      }
      unfold match_res,stateless. reflexivity.
      constructor. reflexivity.
      apply unmodifies_effect_refl.
    }

    intros.
    correct_function_from_body args.
    correct_body.
    unfold f, cl_app.
    rewrite check_mem_aux_eq.

    correct_forward.
    inversion Hcnd.
    simpl.
    apply correct_statement_seq_set with (match_res1 := StateLess _ (nat_correct c)).
    +
      intros MS H.
      unfold INV in H.
      get_invariant _st.
      get_invariant _num.
      get_invariant _perm.
      get_invariant _chunk.
      get_invariant _addr.
      get_invariant _mrs.
      unfold stateless,statefull, eval_inv,is_state_handle in *.
      unfold nat_correct in c5.
      destruct c5 as (c5 & Hrange_mrs_num).
      unfold perm_correct in c6.
      unfold match_chunk, memory_chunk_to_valu32, well_chunk_Z in c7.
      unfold val32_correct in c8.
      destruct c8 as (Hv3_eq & (vi3 & Hc2_eq)).
      unfold mrs_correct, match_regions in c9.
      destruct c9 as (Hv4_eq & Hmrs_eq & (Hmrs_num_eq & Hrange & Hmatch) & _).
      subst.
      eexists.
      split.
      {
        unfold exec_expr.
        rewrite p1.
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
        unfold nat_correct.
        split; [reflexivity| lia].
      }
    constructor.
    simpl.
    reflexivity.
  +
    unfold INV.
    simpl. intuition subst ; discriminate.
  + (**r then here we lose m0 = m? *)
    intros.
    (**r correct_body _ _ (bindM (get_mem_region _ _) ... *)

    correct_forward.

    get_invariant _n.
    get_invariant _mrs.
    get_invariant _st.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1; reflexivity.
    simpl;intros.
    intuition eauto.

    intros.
    (**r goal: correct_body p val (bindM (check_mem_aux2 ... *)

    correct_forward.

    get_invariant _cur_mr.
    get_invariant _perm.
    get_invariant _addr.
    get_invariant _chunk.
    get_invariant _mrs.
    get_invariant _st.
    exists (v::v0::v1::v2::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3; reflexivity.
    simpl;intros.
    unfold correct_get_mem_region.match_res in c4.
    intuition eauto.

    intros.
    (**r goal: correct_body p val (bindM (cmp_ptr32_nullM ... *)

    correct_forward.

    get_invariant _check_mem__1.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    unfold correct_check_mem_aux2.match_res in c4.
    intuition eauto.

    intros.
    (**r modifying here? *)
    correct_forward.
    2:{
        correct_forward.
        get_invariant _check_mem__1.
        eexists ; split_and.
        -
          unfold exec_expr. rewrite p0. reflexivity.
        -
          unfold eval_inv,correct_check_mem_aux2.match_res,stateless in c4.
          subst.
          unfold match_res,eval_inv,stateless.
          reflexivity.
        -simpl.
         apply Cop.cast_val_casted; auto.
        - simpl ; auto.
    }

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
    get_invariant _perm.
    get_invariant _chunk.
    get_invariant _addr.
    get_invariant _mrs.
    exists (v :: v0 :: v1 :: v2 :: v3 :: v4 :: nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3, p4, p5; reflexivity.
    simpl;intros.
    intuition eauto.

    intros.
    get_invariant _is_null.
    unfold exec_expr, Val.of_bool.
    rewrite p0.
    unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
    unfold Vtrue, Vfalse.
    rewrite c4.
    destruct x1; reflexivity.
  + get_invariant _num.
    unfold nat_correct in c4.
    destruct c4 as (Hv_eq & Hrange).
    unfold exec_expr.
    rewrite p0.
    simpl.
    rewrite <- Hv_eq.
    unfold Cop.sem_cmp, Cop.sem_binarith, Val.of_bool, Vfalse; simpl.
    unfold Int.eq.
    change (Int.unsigned (Int.repr 0)) with 0.
    get_invariant _st.
    destruct Hst.
    clear - Hrange mem_regs.
    destruct mem_regs as (_ & Hmrs).
    unfold match_regions in Hmrs.
    change Ptrofs.max_unsigned with Int.max_unsigned in *.
    rewrite Int.unsigned_repr;[ | lia].
    assert (Hneq: (Z.succ (Z.of_nat c)) <> 0). {
      lia.
    }
    eapply zeq_false with (a:= true) (b:= false) in Hneq.
    rewrite Zpos_P_of_succ_nat.
    rewrite Hneq.
    reflexivity.
Qed.

End Check_mem_aux.

Close Scope Z_scope.

Existing Instance correct_function_check_mem_aux.
