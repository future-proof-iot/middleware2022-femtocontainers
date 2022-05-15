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

From bpf.comm Require Import Regs State Monad LemmaNat.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.

(**
Check get_opcode_mem_ld_imm.

get_opcode_mem_ld_imm
     : nat -> M opcode_mem_ld_imm

*)
Open Scope nat_scope.

Section Get_opcode_mem_ld_imm.
  Context {S: special_blocks} .
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode_mem_ld_imm:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_opcode_mem_ld_imm.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_mem_ld_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (opcode_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => StateLess _ (opcode_mem_ld_imm_correct x).

  Instance correct_function_get_opcode_mem_ld_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _op.

    unfold stateless, opcode_correct in c0.
    destruct c0 as (Hc_eq & Hc_range).
    subst.

    eexists. exists m, Events.E0.
    unfold byte_to_opcode_mem_ld_imm.
    split_and; unfold step2.
    -
      forward_star.
      simpl.
      rewrite Int.zero_ext_idem; [| lia].
      rewrite Int.zero_ext_and; [| lia].
      change (two_p 8 - 1)%Z with 255%Z.
      rewrite Int.and_assoc.
      rewrite Int.and_idem.
      forward_star.
    -
      unfold eval_inv, match_res, opcode_mem_ld_imm_correct.
      rewrite Nat_land_0xff; auto.
      destruct (c =? 24) eqn: Hc_eq0;
      [rewrite Nat.eqb_eq in Hc_eq0 | rewrite Nat.eqb_neq in Hc_eq0].
      subst.
      reflexivity.

      destruct (c =? 16) eqn: Hc_eq1;
      [rewrite Nat.eqb_eq in Hc_eq1 | rewrite Nat.eqb_neq in Hc_eq1].
      subst.
      reflexivity.

      assert (Hswitch:
          match c with
          | 16 => op_BPF_LDDW_high
          | 24 => op_BPF_LDDW_low
          | _ => op_BPF_LDX_IMM_ILLEGAL_INS
          end = op_BPF_LDX_IMM_ILLEGAL_INS). {
          do 16 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hc_eq1; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hc_eq0; reflexivity | reflexivity ].
        }
        rewrite Hswitch; clear Hswitch.
        exists c.
        split; [ | split; [split |]; assumption].
        unfold Int.and.
        change (Int.unsigned (Int.repr 255)) with (Z.of_nat (Z.to_nat 255%Z)).
        rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
        rewrite land_land.
        change (Z.to_nat 255) with 255.
        rewrite Nat_land_0xff; auto.
    - constructor.
      simpl.
      rewrite Int.zero_ext_and.
      change (two_p 8 - 1)%Z with 255%Z.
      rewrite Int.and_assoc.
      rewrite Int.and_idem.
      reflexivity.
      lia.
    - auto.
    - apply unmodifies_effect_refl.
  Qed.

End Get_opcode_mem_ld_imm.

Close Scope nat_scope.

Existing Instance correct_function_get_opcode_mem_ld_imm.
