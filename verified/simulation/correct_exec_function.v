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

From bpf.clightlogic Require Import clight_exec Clightlogic CommonLemma CorrectRel.

From bpf.simulation Require Import MatchState InterpreterRel.

(*
Check exec_function.
exec_function
     : val -> M val
*)

Section Exec_function.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [(val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := exec_function.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_exec_function.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun x => StateLess _ (is_state_handle))
      (dcons (fun x => StateLess _ (eq x))
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun r  => StateLess _ (val32_correct r).

  Axiom correct_function_exec_function : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.

End Exec_function.

Existing Instance correct_function_exec_function.
