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

From bpf.comm Require Import MemRegion State Monad.
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
Check get_block_perm.

get_block_perm
     : memory_region -> DxMonad.M permission
*)

Section Get_block_perm.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_region:Type)].
  Definition res : Type := (permission:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_block_perm.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_block_perm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (statefull (match_region st_blk mrs_blk ins_blk))
       (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := stateless perm_correct.

  Instance correct_function_get_block_perm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _mr.

    unfold match_region in c0.
    destruct c0 as (o & Hptr & Hmatch).
    unfold match_region_at_ofs in Hmatch.
    destruct Hmatch as (_ & _ & (vperm & Hperm_load & Hinj) & _).
    subst.

    (**according to the type:
         static unsigned long long getMemRegion_start_addr(struct memory_region *mr1)
       1. return value should be  `Vlong vaddr`
       2. the memory is same
      *)
    exists (Vint vperm), m, Events.E0.

    split_and; unfold step2.
    -
      repeat forward_star.
      unfold align, Ctypes.alignof; simpl.
      unfold Mem.loadv in Hperm_load.
      rewrite Hperm_load; reflexivity.

      Transparent Archi.ptr64.
      reflexivity.
    - unfold eval_inv,match_res. simpl. unfold correct_perm in Hinj. unfold perm_correct.
      destruct (block_perm c); rewrite Hinj; reflexivity.
    - constructor. reflexivity.
    - auto.
    - apply unmodifies_effect_refl.
  Qed.

End Get_block_perm.

Existing Instance correct_function_get_block_perm.
