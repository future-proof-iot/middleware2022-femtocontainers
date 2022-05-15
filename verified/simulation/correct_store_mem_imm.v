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

From bpf.comm Require Import State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clight Require Import interpreter.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import MatchState InterpreterRel.

(**

Check store_mem_imm.
store_mem_imm
     : val -> memory_chunk -> val -> M unit

 *)

Section Store_mem_imm.
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [val; (memory_chunk:Type); val].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := store_mem_imm.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_store_mem_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle)
      (dcons (fun x => StateLess _ (eq x))
         (dcons (fun x => StateLess _ (match_chunk x))
            (dcons (fun x => StateLess _ (val32_correct x))
              (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x => StateLess _ (eq Vundef).

  Instance correct_function_store_mem_imm : forall ptr ck v, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res (DList.DCons ptr
      (DList.DCons ck
         (DList.DCons v
              (DList.DNil _)))).
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, store_mem_imm, State.store_mem_imm, Mem.storev, INV, app.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  get_invariant _v.
  unfold eval_inv, is_state_handle in *.
  unfold match_chunk in c0.
  unfold val32_correct in c2.
  destruct c2 as (Hc1_eq & vi & Hvi_eq).
  subst.

  unfold rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z in p1.
  unfold match_res.
  unfold vint_to_vint_or_vlong.
  destruct ck; try constructor.
  all: destruct v2; try constructor.
  all: destruct Mem.store eqn: Hstore; [| constructor].
  all: eapply store_reg_preserive_match_state in MS as Hstore_m2; eauto.
  all: destruct Hstore_m2 as (m2 & Hstore_m2 & Hmatch_m2).
  all: intros; exists Vundef, m2, Events.E0.
  - (**r c = Mint8unsigned *)
    split_and; auto.
    + forward_star.
    change (Int.unsigned (Int.repr 1)) with 1%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
  - (**r c = Mint16unsigned *)
    split_and; auto.
    + forward_star.
    change (Int.unsigned (Int.repr 2)) with 2%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
  - (**r c = Mint32 *)
    split_and; auto.
    + forward_star.
    change (Int.unsigned (Int.repr 4)) with 4%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
  - (**r c = Mint64 *)
    split_and; auto.
    + forward_star.
    change (Int.unsigned (Int.repr 8)) with 8%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
Qed.

End Store_mem_imm.

Existing Instance correct_function_store_mem_imm.
