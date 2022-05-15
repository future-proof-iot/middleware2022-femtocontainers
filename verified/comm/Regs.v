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

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory.
From compcert.lib Require Import Integers.

From bpf.comm Require Import rBPFValues.
From Coq Require Import List ZArith.
Import ListNotations.


Inductive reg: Type :=
  | R0:reg | R1:reg | R2:reg
  | R3:reg | R4:reg | R5:reg
  | R6:reg | R7:reg | R8:reg
  | R9:reg | R10:reg
.

Lemma reg_eq: forall (x y: reg), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

Definition reg_eqb (r0 r1: reg) : bool :=
  match r0, r1 with
  | R0, R0
  | R1, R1
  | R2, R2
  | R3, R3
  | R4, R4
  | R5, R5
  | R6, R6
  | R7, R7
  | R8, R8
  | R9, R9
  | R10, R10 => true
  | _, _ => false
  end.

Lemma reg_eqb_true:
  forall x y, x = y <-> reg_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma reg_eqb_false:
  forall x y, x <> y <-> reg_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Record regmap: Type := make_regmap{
  r0_val  : Values.val;
  r1_val  : Values.val;
  r2_val  : Values.val;
  r3_val  : Values.val;
  r4_val  : Values.val;
  r5_val  : Values.val;
  r6_val  : Values.val;
  r7_val  : Values.val;
  r8_val  : Values.val;
  r9_val  : Values.val;
  r10_val : Values.val;
}.

Definition eval_regmap (r:reg) (regs:regmap): val := 
  match r with
  | R0  => r0_val regs
  | R1  => r1_val regs
  | R2  => r2_val regs
  | R3  => r3_val regs
  | R4  => r4_val regs
  | R5  => r5_val regs
  | R6  => r6_val regs
  | R7  => r7_val regs
  | R8  => r8_val regs
  | R9  => r9_val regs
  | R10 => r10_val regs
  end.

Definition upd_regmap (r:reg) (v:val) (regs:regmap): regmap :=
  match r with
  | R0  => 
    {|
      r0_val  := v;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R1  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := v;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |}
  | R2  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := v;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R3  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := v;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R4  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := v;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R5  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := v;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R6  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := v;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R7  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := v;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R8  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := v;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R9  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := v;
      r10_val := r10_val regs;
    |} 
  | R10 => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := v;
    |} 
  end.

Definition val64_zero := Vlong Int64.zero.

Definition init_regmap: regmap := {|
  r0_val  := val64_zero;
  r1_val  := val64_zero;
  r2_val  := val64_zero;
  r3_val  := val64_zero;
  r4_val  := val64_zero;
  r5_val  := val64_zero;
  r6_val  := val64_zero;
  r7_val  := val64_zero;
  r8_val  := val64_zero;
  r9_val  := val64_zero;
  r10_val := val64_zero;
|}.
