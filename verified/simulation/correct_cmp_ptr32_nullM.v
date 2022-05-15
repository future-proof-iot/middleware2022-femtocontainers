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

From bpf.comm Require Import MemRegion State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.clightlogic Require Import clight_exec Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


(**
Check cmp_ptr32_nullM.

cmp_ptr32_nullM
     : val -> M bool

static __attribute__((always_inline)) inline _Bool cmp_ptr32_nullM(struct bpf_state* st, unsigned char* addr){
   return (addr == 0);
}
*)

Section Cmp_ptr32_nullM.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := cmp_ptr32_nullM.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_cmp_ptr32_nullM.

  (* [match_arg] relates the Coq arguments and the C arguments *)
(*  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    DList.DCons (val_ptr_correct state_block mrs_block ins_block)
        (DList.DNil _). *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (eq x))
        (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => StateLess _ (match_bool x).

  Lemma cmpu_valid_pointer : forall m m'
    (VALID : forall blk ofs, Mem.valid_pointer m blk ofs = true ->
       Mem.valid_pointer m' blk ofs = true) v b,
      Val.cmpu_bool (Mem.valid_pointer m) Ceq v
          (Vint Int.zero) = Some b ->
      Val.cmpu_bool (Mem.valid_pointer m') Ceq v
          (Vint Int.zero) = Some b.
  Proof.
    unfold Val.cmpu_bool.
    intros.
    destruct v; auto.
    destruct Archi.ptr64 eqn:A; auto.
    destruct (Int.eq Int.zero Int.zero &&
                (Mem.valid_pointer m b0 (Ptrofs.unsigned i)
                 || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))
             ) eqn: T; try discriminate.
    destruct     (Int.eq Int.zero Int.zero &&
    (Mem.valid_pointer m' b0 (Ptrofs.unsigned i)
     || Mem.valid_pointer m' b0 (Ptrofs.unsigned i - 1))) eqn:T';auto.
    rewrite andb_true_iff in T.
    rewrite orb_true_iff in T.
    rewrite andb_false_iff in T'.
    rewrite orb_false_iff in T'.
    intuition try congruence.
    apply VALID in H2. congruence.
    apply VALID in H2. congruence.
  Qed.

  
  Instance correct_function_cmp_ptr32_nullM : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, cmp_ptr32_nullM, app.
    repeat intro.
    get_invariant _addr.

    unfold eval_inv in c0.
    subst.
    destruct (rBPFValues.cmp_ptr32_null (State.eval_mem st) v) eqn: CMP ; auto.
    exists (Val.of_bool b).
    exists m. exists Events.E0.
    unfold rBPFValues.cmp_ptr32_null in CMP.
    change Vnullptr with (Vint Int.zero) in *; simpl.
    split_and; auto.
    -
      apply cmpu_valid_pointer with (m':= m) in CMP.
      unfold step2; forward_star.
      unfold Cop.sem_binary_operation, typeof; simpl.
      unfold Cop.sem_cmp; simpl.
      unfold Cop.cmp_ptr; simpl.
      change (Int.repr 0) with (Int.zero).
      rewrite CMP. reflexivity.
      unfold Cop.sem_cast; simpl.
      instantiate (1:= (Val.of_bool b)).
      destruct b; reflexivity.
      forward_star.
      intros *.
      eapply match_state_implies_valid_pointer ; eauto.
    -  unfold match_bool. destruct b; reflexivity.
    -  destruct b; constructor.
       reflexivity. reflexivity.
  Qed.

End Cmp_ptr32_nullM.

Existing Instance correct_function_cmp_ptr32_nullM.
