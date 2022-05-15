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

From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues rBPFMonadOp.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import MatchState InterpreterRel.


(*
Check _bpf_get_call.
_bpf_get_call
     : val -> M val
*)

Section Bpf_get_call.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [(val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := _bpf_get_call.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f__bpf_get_call.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv State.state) args :=
      (dcons (fun x => StateLess State.state (val32_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun r  => StateLess State.state (eq r).

  Axiom correct_function__bpf_get_call : forall a, correct_function State.state p args res f fn ModNothing true match_state match_arg_list match_res a.

End Bpf_get_call.

Existing Instance correct_function__bpf_get_call.
