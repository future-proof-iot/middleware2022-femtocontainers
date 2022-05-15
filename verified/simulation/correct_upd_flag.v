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

From bpf.comm Require Import Flag State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


Section Upd_flag.
  Context {S :special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(bpf_flag:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := upd_flag.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_flag.

  Definition modifies  := ModSomething. (* of the C code *)

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
   dcons (fun x =>  StateLess _ (is_state_handle))
                (dcons (fun x => (StateLess _ (flag_correct x)))
                             (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x => StateLess _ (fun v => v = Vundef).

  Instance correct_function_upd_flag : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    get_invariant _f.
    unfold eval_inv, is_state_handle in c0.
    unfold eval_inv, flag_correct in c1.
    subst.

    simpl in c.
    assert (Hst2 := MS).
    apply (upd_flags_store  _ _ (int_of_flag c)) in Hst2 as Hstore.
    destruct Hstore as (m1 & Hstore).
    (** we need to get the value of flag in the memory *)
    set (Hst' := MS).
    destruct Hst' as (_, _ , Hflag, _, _, _, _, _, _, _).
    unfold Mem.loadv in Hflag.
    
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static void upd_flag(struct bpf_state* st, int f)
       1. return value should be Vundef
       2. the memory is m_flag
      *)
    exists Vundef, m1, Events.E0.

    split_and; unfold step2.
    - repeat forward_star.
    - simpl. reflexivity.
    - constructor.
    -
      eapply upd_flag_preserves_match_state. eauto.
      reflexivity.
      apply Hstore.
    - exact I.
  Qed.

End Upd_flag.

Existing  Instance correct_function_upd_flag.
