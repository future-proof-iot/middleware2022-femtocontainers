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

Check get_opcode_mem_ld_reg.
get_opcode_mem_ld_reg
     : nat -> M opcode_mem_ld_reg

*)

Open Scope nat_scope.
Section Get_opcode_mem_ld_reg.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode_mem_ld_reg:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_opcode_mem_ld_reg.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_mem_ld_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (opcode_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => (StateLess _ (opcode_mem_ld_reg_correct x)).

  Instance correct_function_get_opcode_mem_ld_reg : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _op.

    unfold eval_inv, opcode_correct in c0.
    destruct c0 as (Hc_eq & Hc_range).
    subst.

    eexists. exists m, Events.E0.
    unfold byte_to_opcode_mem_ld_reg.
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
      unfold match_res, opcode_mem_ld_reg_correct.
      rewrite Nat_land_0xff; auto.
      destruct (c =? 97) eqn: Hldxw;
      [rewrite Nat.eqb_eq in Hldxw; subst; reflexivity | rewrite Nat.eqb_neq in Hldxw].
      destruct (c =? 105) eqn: Hldxh;
      [rewrite Nat.eqb_eq in Hldxh; subst; reflexivity | rewrite Nat.eqb_neq in Hldxh].
      destruct (c =? 113) eqn: Hldxb;
      [rewrite Nat.eqb_eq in Hldxb; subst; reflexivity | rewrite Nat.eqb_neq in Hldxb].
      destruct (c =? 121) eqn: Hldxdw;
      [rewrite Nat.eqb_eq in Hldxdw; subst; reflexivity | rewrite Nat.eqb_neq in Hldxdw].

      assert (Hswitch:
          match c with
          | 97 => op_BPF_LDXW
          | 105 => op_BPF_LDXH
          | 113 => op_BPF_LDXB
          | 121 => op_BPF_LDXDW
          | _ => op_BPF_LDX_REG_ILLEGAL_INS
          end = op_BPF_LDX_REG_ILLEGAL_INS). {
          do 97 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hldxw; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hldxh; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hldxb; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hldxdw; reflexivity | reflexivity].
        }
        rewrite Hswitch; clear Hswitch.
        exists c.
        split; [ | intuition ].
        unfold Int.and.
        change (Int.unsigned (Int.repr 255)) with (Z.of_nat (Z.to_nat 255%Z)).
        rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
        rewrite LemmaNat.land_land.
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

End Get_opcode_mem_ld_reg.

Close Scope nat_scope.

Existing Instance correct_function_get_opcode_mem_ld_reg.
