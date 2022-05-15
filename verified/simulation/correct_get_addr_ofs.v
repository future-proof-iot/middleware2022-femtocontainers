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

From bpf.comm Require Import State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
unsigned int get_addr_ofs(unsigned long long x, int ofs)
{
  return (unsigned int) (x + (unsigned long long) ofs);
}

Print get_addr_ofs.
get_addr_ofs = 
fun (x : val64_t) (ofs : sint32_t) =>
returnM (val_intuoflongu (Val.addl x (Val.longofintu (sint32_to_vint ofs))))
     : val64_t -> sint32_t -> M valu32_t

*)

Section Get_addr_ofs.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (int:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_addr_ofs.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_addr_ofs.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (stateless val64_correct)
       (dcons (stateless sint32_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := stateless val32_correct.

  Instance correct_function_get_addr_ofs : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _x.
    get_invariant _ofs.

    unfold stateless, eval_inv, val64_correct in c1.
    unfold stateless, eval_inv, sint32_correct in c2.
    destruct c1 as (Hc_eq & (vi & Hvi_eq)).
    destruct c2 as (c2 & c2_range).
    subst c v v0.

    (**according to the type of eval_pc:
unsigned int get_addr_ofs(unsigned long long x, int ofs)
{
  return (unsigned int) (x + (unsigned long long) ofs);
}
       1. return value should be  x+y
       2. the memory is same
      *)
    eexists. exists m, Events.E0.

    split_and; unfold step2;auto.
    -
      repeat forward_star.
    - simpl. unfold val32_correct. eauto.
    - simpl.
      constructor.
      reflexivity.
    - apply unmodifies_effect_refl.
  Qed.

End Get_addr_ofs.

Existing Instance correct_function_get_addr_ofs.
