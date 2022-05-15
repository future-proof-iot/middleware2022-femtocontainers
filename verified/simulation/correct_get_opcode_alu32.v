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
Check get_opcode_alu32.
get_opcode_alu32
     : nat -> M opcode_alu32

*)

Section Get_opcode_alu32.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode_alu32:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_opcode_alu32.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_alu32.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (opcode_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => StateLess _ (opcode_alu32_correct x).

  Instance correct_function_get_opcode_alu32 : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
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
    unfold eval_inv,match_res.
    eexists. exists m, Events.E0.

    split_and; unfold step2.
    -
      repeat forward_star.
    - simpl.
      unfold opcode_alu32_correct.
      (**r Search (Int.zero_ext).*)
      rewrite Int.zero_ext_idem;[idtac | lia].
      unfold match_res, opcode_alu32_correct.
      rewrite byte_to_opcode_alu32_if_same.
      unfold byte_to_opcode_alu32_if.
      rewrite Int.zero_ext_and; [| lia].
      rewrite nat8_land_240_255_eq; [| apply Hge].

      simpl_opcode Hadd.
      simpl_opcode Hsub.
      simpl_opcode Hmul.
      simpl_opcode Hdiv.
      simpl_opcode Hor.
      simpl_opcode Hand.
      simpl_opcode Hlsh.
      simpl_opcode Hrsh.
      simpl_opcode Hneg.
      simpl_opcode Hmod.
      simpl_opcode Hxor.
      simpl_opcode Hmov.
      simpl_opcode Harsh.
      exists c; split; [reflexivity| idtac].
      unfold is_illegal_alu32_ins.
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

End Get_opcode_alu32.

Existing Instance correct_function_get_opcode_alu32.
