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

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.


(**
Check get_opcode.
get_opcode
     : int64 -> M nat
*)

Open Scope Z_scope.

Section Get_opcode.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (nat:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := get_opcode.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (int64_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x  => StateLess _ (opcode_correct x).

  Instance correct_function_bpf_verifier_get_opcode : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f. unfold get_opcode.
    correct_forward.

    get_invariant _ins.

    unfold eval_inv, int64_correct in c0.
    subst.

    eexists.

    assert (Hc_le: (0 <= Z.land (Int64.unsigned c) 255 <= 255)%Z). {
      assert (Heq: (Int64.unsigned c) = Z.of_nat (Z.to_nat(Int64.unsigned c))). {
        rewrite Z2Nat.id.
        reflexivity.
        assert (Hrange: (0 <= Int64.unsigned c < Int64.modulus)%Z) by apply Int64.unsigned_range.
        lia.
      }
      rewrite Heq; clear.
      change 255%Z with (Z.of_nat (Z.to_nat 255%Z)) at 1 2.
      rewrite LemmaNat.land_land.
      split.
      lia.
      assert (H: ((Nat.land (Z.to_nat (Int64.unsigned c)) (Z.to_nat 255)) <= 255)%nat). {
        rewrite Nat.land_comm.
        rewrite LemmaNat.land_bound.
        lia.
      }
      lia.
    }

    split_and; auto.
    {
      unfold exec_expr. repeat
      match goal with
      | H: ?X = _ |- context [match ?X with _ => _ end] =>
        rewrite H
      end. simpl.
      unfold Cop.sem_cast; simpl.
      rewrite Int.zero_ext_and; [| lia].
      change (two_p 8 - 1)%Z with 255%Z.

      unfold Int64.and.
      change (Int64.unsigned (Int64.repr 255)) with 255%Z.
      rewrite Int64.unsigned_repr; [ | change Int64.max_unsigned with 18446744073709551615%Z; lia].

      unfold Int.and.
      rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
      change (Int.unsigned (Int.repr 255)) with 255%Z.
      rewrite <- Z.land_assoc.
      rewrite Z.land_diag.
      reflexivity.
    }

    unfold eval_inv, match_res, BinrBPF.get_opcode.
    unfold opcode_correct.
    unfold Int64.and.
    change (Int64.unsigned (Int64.repr 255)) with 255%Z.
    rewrite Int64.unsigned_repr; [ | change Int64.max_unsigned with 18446744073709551615%Z; lia].

    rewrite Z2Nat.id; [| lia].
    split; [reflexivity | lia].

    unfold Cop.sem_cast; simpl.
    rewrite Int.zero_ext_and; [| lia].
    change (two_p 8 - 1)%Z with 255%Z.
    unfold Int.and.
    rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
    change (Int.unsigned (Int.repr 255)) with 255%Z.
    rewrite <- Z.land_assoc.
    reflexivity.
  Qed.

End Get_opcode.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_get_opcode.
