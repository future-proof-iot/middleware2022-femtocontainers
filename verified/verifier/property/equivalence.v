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

From compcert Require Import Integers Values AST Ctypes.
From Coq Require Import ZArith Lia.

From bpf.comm Require Import BinrBPF.
From bpf.verifier.comm Require Import state monad.
From bpf.verifier.dxmodel Require Import Dxverifier.
From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.


Open Scope Z_scope.


Theorem bpf_verifier_equilence_dx_synthesis:
  forall st,
    Dxverifier.bpf_verifier st = bpf_verifier st.
Proof.
  intros.
  unfold Dxverifier.bpf_verifier, bpf_verifier.
  unfold Dxmonad.bindM, Dxmonad.returnM.
  unfold Dxmonad.eval_ins_len.
  unfold rBPFValues.Int_leu.
  unfold DxNat.nat2int, DxIntegers.int32_1.
  unfold DxIntegers.int32_max_unsigned, DxIntegers.int32_8.
  unfold Dxmonad.eval_ins, DxIntegers.int64_t, DxNat.nat32_1, DxIntegers.int64_0x95.
  f_equal.
Qed.
