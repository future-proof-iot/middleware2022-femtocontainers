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

From bpf.comm Require Import Regs BinrBPF State Monad.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.

(**
Check get_opcode_ins.
get_opcode_ins
     : int64 -> M nat

*)

Section Get_opcode_ins.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (nat:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := get_opcode_ins.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_ins.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (int64_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => StateLess _ (opcode_correct x).

  Instance correct_function_get_opcode_ins : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _ins.

    unfold eval_inv, int64_correct in c0.
    subst.

    eexists. exists m, Events.E0.
    unfold match_res, opcode_correct, BinrBPF.get_opcode.

    unfold Int64.and.
    change (Int64.unsigned (Int64.repr 255)) with 255%Z.
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
    rewrite Int64.unsigned_repr; [ | change Int64.max_unsigned with 18446744073709551615%Z; lia].

    rewrite Z2Nat.id; [| lia].

    split; unfold step2.
    -
      forward_star.
      simpl.
      rewrite Int.zero_ext_idem; [| lia].
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

      unfold step2; forward_star.
    - split.
      + unfold eval_inv.
        split; [reflexivity|].
        lia.
      + split.
        * constructor.
          simpl.
          rewrite Int.zero_ext_and; [| lia].
          change (two_p 8 - 1)%Z with 255%Z.

          unfold Int.and.
          rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
          change (Int.unsigned (Int.repr 255)) with 255%Z.
          rewrite <- Z.land_assoc.
          rewrite Z.land_diag.
          reflexivity.
        * split; [auto|].
          apply unmodifies_effect_refl.
  Qed.

End Get_opcode_ins.

Existing Instance correct_function_get_opcode_ins.
