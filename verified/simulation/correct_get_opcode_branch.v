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
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check get_opcode_branch.
get_opcode_branch
     : nat8 -> DxMonad.M opcode_branch

*)

Section Get_opcode_branch.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode_branch:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_opcode_branch.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_branch.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (opcode_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => StateLess _ (opcode_branch_correct x).

  Instance correct_function_get_opcode_branch : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _op.

    unfold eval_inv, opcode_correct in c0.
    destruct c0 as (H0 & Hge).
    subst.

    eexists. exists m, Events.E0.

    split_and; unfold step2.
    -
      repeat forward_star.
    - simpl.
      unfold opcode_branch_correct.
      (**r Search (Int.zero_ext).*)
      rewrite Int.zero_ext_idem;[idtac | lia].
      unfold match_res, opcode_branch_correct.
      rewrite byte_to_opcode_branch_if_same.
      unfold byte_to_opcode_branch_if.
      rewrite Int.zero_ext_and; [change (Int.repr (two_p 8 - 1)) with (Int.repr 255) | lia].
      rewrite nat8_land_240_255_eq; [| apply Hge].
      simpl_opcode Hja.
      simpl_opcode Hjeq.
      simpl_opcode Hjgt.
      simpl_opcode Hjge.
      simpl_opcode Hjlt.
      simpl_opcode Hjle.
      simpl_opcode Hjset.
      simpl_opcode Hjne.
      simpl_opcode Hjsgt.
      simpl_opcode Hjsge.
      simpl_opcode Hjsjt.
      simpl_opcode Hjsle.
      simpl_opcode Hcall.
      simpl_opcode Hret.
      exists c.
      split; [reflexivity |].
      unfold is_illegal_jmp_ins.
      repeat simpl_land H0.
    - simpl.
      constructor.
      rewrite Int.zero_ext_idem;[idtac | lia].
      simpl.
      rewrite Int.zero_ext_idem;[idtac | lia].
      reflexivity.
    - auto.
    - apply unmodifies_effect_refl.
  Qed.

End Get_opcode_branch.

Existing Instance correct_function_get_opcode_branch.
