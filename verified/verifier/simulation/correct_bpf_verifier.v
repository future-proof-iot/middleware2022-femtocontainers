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
From bpf.verifier.simulation Require Import correct_bpf_verifier_eval_ins_len  correct_bpf_verifier_eval_ins correct_bpf_verifier_aux.


(**
Check bpf_verifier.
bpf_verifier
     : M state.state bool

*)
Open Scope Z_scope.

Section Bpf_verifier.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun _ => StateLess _ is_state_handle)
      (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

  Instance correct_function_bpf_verifier : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier.
    unfold INV.

    correct_forward.

    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    intuition eauto.
    intros.

    correct_forward.
    { correct_forward.
      { correct_forward.

        get_invariant _st.
        get_invariant _len.
        exists (v::v0::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold eval_inv, correct_bpf_verifier_eval_ins_len.match_res in c0.
        intuition eauto.
        intros.

        correct_forward.
        { correct_forward.

          get_invariant _st.
          get_invariant _len.
          unfold eval_inv, correct_bpf_verifier_eval_ins_len.match_res in c0.
          unfold nat_correct in c0.
          destruct c0 as (c0 & Hc0_range).
          exists (v::(Vint (Int.sub (Int.repr (Z.of_nat x)) (Int.repr 1)))::nil).
          split.
          unfold map_opt, exec_expr. rewrite p0,p1.
          rewrite <- c0.
          simpl. reflexivity.
          intros; simpl.
          intuition eauto.
          unfold uint32_correct.
          unfold Int.sub.
          change (Int.unsigned (Int.repr 1)) with 1.
          rewrite Int.unsigned_repr.
          split; [f_equal | rewrite Int.unsigned_repr; lia].
          f_equal.
          change 1 with (Z.of_nat 1).
          apply Nat2Z.inj_sub.
          apply Cle_Zle_unsigned in Hcnd.
          change (Int.unsigned Int.one) with 1 in Hcnd.
          rewrite Int.unsigned_repr in Hcnd.
          lia.
          lia.
          lia.
          intros.

          correct_forward.
          unfold match_res.

          get_invariant _ins64.
          exists (Val.of_bool (Int64.eq x1 (Int64.repr 149))).
          unfold exec_expr, eval_inv.
          rewrite p0.
          unfold eval_inv, correct_bpf_verifier_eval_ins.match_res in c.
          unfold int64_correct in c.
          rewrite <- c.
          simpl.
          split.
          unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
          reflexivity.
          unfold bool_correct, Val.of_bool.
          split; [destruct Int64.eq; reflexivity |].
          unfold Cop.sem_cast; simpl.
          split; [destruct Int64.eq; reflexivity |].
          intros.
          destruct Int64.eq; constructor; reflexivity.
        }

        correct_forward.
        unfold match_res.
        exists (Vint (Int.repr 0)).
        unfold exec_expr, eval_inv.
        split; [reflexivity |].
        unfold bool_correct; simpl.
        fold Int.zero.
        split; [reflexivity |].
        unfold Cop.sem_cast; simpl.
        rewrite Int.eq_true.
        split; [reflexivity |].
        intros.
        constructor.
        reflexivity.

        get_invariant _b.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, correct_bpf_verifier_aux.match_res, bool_correct in c.
        rewrite c.
        unfold Val.of_bool; simpl.
        unfold Vtrue, Vfalse.
        destruct x0; reflexivity.
      }

      correct_forward.
      unfold match_res.
      exists (Vint (Int.repr 0)).
      unfold exec_expr, eval_inv.
      split; [reflexivity |].
      unfold bool_correct; simpl.
      fold Int.zero.
      split; [reflexivity |].
      unfold Cop.sem_cast; simpl.
      rewrite Int.eq_true.
      split; [reflexivity |].
      intros.
      constructor.
      reflexivity.

      get_invariant _len.
      unfold exec_expr.
      rewrite p0.
      unfold eval_inv, correct_bpf_verifier_eval_ins_len.match_res, nat_correct in c.
      destruct c as (c & Hc_range).
      rewrite <- c.
      unfold Cop.sem_binary_operation, typeof; simpl.
      unfold Cop.sem_div, Cop.sem_binarith; simpl.
      change (Int.eq (Int.repr 8) Int.zero) with false.
      unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
      unfold Val.of_bool.
      change (Int.divu (Int.repr (-1)) (Int.repr 8)) with (Int.repr 536870911).
      change (Int.divu (Int.repr Int.max_unsigned) (Int.repr 8)) with (Int.repr 536870911).

      assert (Heq: Z.of_nat (Z.to_nat Ptrofs.max_unsigned / 8) = 536870911). {
        rewrite div_Zdiv; [| intro Hfalse; inversion Hfalse].
        rewrite Z2Nat.id.
        change Ptrofs.max_unsigned with 4294967295.
        reflexivity.
        change Ptrofs.max_unsigned with 4294967295.
        lia.
      }

      f_equal.
    }
    { correct_forward.
      unfold match_res.
      exists (Vint (Int.repr 0)).
      unfold exec_expr, eval_inv.
      split; [reflexivity |].
      unfold bool_correct; simpl.
      fold Int.zero.
      split; [reflexivity |].
      unfold Cop.sem_cast; simpl.
      rewrite Int.eq_true.
      split; [reflexivity |].
      intros.
      constructor.
      reflexivity.
    }

    get_invariant _len.
    unfold exec_expr.
    rewrite p0.
    unfold eval_inv, correct_bpf_verifier_eval_ins_len.match_res, nat_correct in c.
    destruct c as (c & Hc_range).
    rewrite <- c.
    unfold Cop.sem_binary_operation, typeof; simpl.
    unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
    unfold Val.of_bool.

    unfold Int.one.
    f_equal.
Qed.

End Bpf_verifier.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier.
