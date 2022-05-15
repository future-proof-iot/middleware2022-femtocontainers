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

From bpf.comm Require Import Regs State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory Memdata.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check upd_reg.
upd_reg
     : reg -> val64_t -> M unit
 *)


Section Upd_reg.
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(reg:Type);val].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := upd_reg.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_reg.

  Definition modifies  := ModSomething. (* of the C code *)

  (* [match_arg] relates the Coq arguments and the C arguments *)


Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ (is_state_handle))
      (dcons (fun x => StateLess _ (reg_correct x))
        (dcons (fun x => StateLess _ (val64_correct x))
          (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun _  => StateLess _ (fun v => v = Vundef).

  Instance correct_function_upd_reg : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    get_invariant _i.
    get_invariant _v.
    unfold eval_inv,is_state_handle in c1.
    unfold eval_inv, reg_correct in c2.
    unfold eval_inv, val64_correct in c3.
    destruct c3 as (Hc_eq & (vl & Hvl_eq)).
    subst.
    simpl in c.
    apply (upd_regs_store m _ c vl) in MS as Hstore.
    destruct Hstore as (m1 & Hstore).

    (**according to the type:
         static void upd_reg (struct bpf_state* st, unsigned int i, unsigned long long v)
       1. return value should be Vundef (i.e. void)
       2. the new memory should change the value of reg, i.e. m_reg
      *)
    exists Vundef, m1, Events.E0.

    split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.

      unfold Coqlib.align; simpl.
      rewrite Ptrofs.add_zero_l.
      assert (Heq: (8 + 8 * id_of_reg c)%Z = (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 8) (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (Int.repr (id_of_reg c))))))). {
        unfold Ptrofs.add, Ptrofs.mul.
        unfold id_of_reg; destruct c; try unfold Ptrofs.of_intu, Ptrofs.of_int; repeat rewrite Ptrofs.unsigned_repr; try rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try rewrite Ptrofs_max_unsigned_eq32; try lia.
      }
      rewrite <- Heq.
      rewrite <- Hstore; reflexivity.
    - split_and.
      + simpl. reflexivity.
      + constructor.
      + eapply upd_reg_preserves_match_state.
        apply MS.
        reflexivity.
        apply Hstore.
      + simpl; auto.
Qed.

End Upd_reg.

Existing Instance correct_function_upd_reg.
