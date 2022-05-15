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

From compcert Require Import Ctypes AST Integers.
From Coq Require Import ZArith.

From bpf.comm Require Import Regs rBPFAST.

(** For use to distinguish ALU32 and ALU64 *)
Inductive arch := A32 | A64.

Lemma arch_eq: forall (x y: arch), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

Definition arch_eqb (a0 a1: arch) : bool :=
  match a0, a1 with
  | A32, A32
  | A64, A64 => true
  | _, _ => false
  end.

Lemma arch_eqb_true:
  forall x y, x = y <-> arch_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma arch_eqb_false:
  forall x y, x <> y <-> arch_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Definition arch2Z (a: arch) : Z :=
  match a with
  | A32 => 32%Z
  | A64 => 64%Z
  end.

(** For condition flags *)
(*Inductive signedness := Signed | Unsigned.*)

Inductive cond := 
  Eq 
| Gt: signedness -> cond 
| Ge: signedness -> cond
| Lt: signedness -> cond
| Le: signedness -> cond
| SEt 
| Ne
.

Lemma signedness_eq32: forall (s1 s2: signedness), {s1=s2} + {s1<>s2}.
Proof.
  decide equality.
Defined.

Definition signedness_eqb (s1 s2: signedness) :=
  match s1, s2 with
  | Signed, Signed
  | Unsigned, Unsigned => true
  | _, _ => false
  end.

Lemma signedness_eqb_true:
  forall x y, x = y <-> signedness_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma signedness_eqb_false:
  forall x y, x <> y <-> signedness_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma cond_eq: forall (x y: cond), {x=y} + {x<>y}.
Proof.
  decide equality. all: apply signedness_eq32.
Defined.

Definition cond_eqb (c0 c1: cond): bool :=
  match c0, c1 with
  | Eq, Eq
  | SEt, SEt
  | Ne, Ne => true
  | Gt s0, Gt s1
  | Ge s0, Ge s1
  | Lt s0, Lt s1
  | Le s0, Le s1 => signedness_eqb s0 s1
  | _, _ => false
  end.

Lemma cond_eqb_true:
  forall x y, x = y <-> cond_eqb x y = true.
Proof.
  unfold cond_eqb.
  destruct x, y; simpl; try (rewrite <- signedness_eqb_true); intuition congruence.
Qed.

Lemma cond_eqb_false:
  forall x y, x <> y <-> cond_eqb x y = false.
Proof.
  unfold cond_eqb.
  destruct x, y; simpl; try (rewrite <- signedness_eqb_false); intuition congruence.
Qed.

Definition off := int.
Definition imm := int.

Inductive binOp: Type :=
  BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND
| BPF_LSH | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV| BPF_ARSH.

Lemma binOp_eq: forall (b1 b2: binOp), {b1=b2} + {b1<>b2}.
Proof.
  decide equality.
Defined.

Definition binOp_eqb (b0 b1: binOp): bool :=
  match b0, b1 with
  | BPF_ADD, BPF_ADD
  | BPF_SUB, BPF_SUB
  | BPF_MUL, BPF_MUL
  | BPF_DIV, BPF_DIV
  | BPF_OR,  BPF_OR
  | BPF_AND, BPF_AND
  | BPF_LSH, BPF_LSH
  | BPF_RSH, BPF_RSH
  | BPF_MOD, BPF_MOD
  | BPF_XOR, BPF_XOR
  | BPF_MOV, BPF_MOV
  | BPF_ARSH, BPF_ARSH => true
  | _, _ => false
  end.

Lemma binOp_eqb_true:
  forall x y, x = y <-> binOp_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma binOp_eqb_false:
  forall x y, x <> y <-> binOp_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

(**r BPD_LDDW are splitted into BPD_LDDW_low and BPD_LDDW_high *)

Inductive instruction: Type :=
  (**r ALU64/32*)
  | BPF_NEG    : arch -> reg -> instruction
  | BPF_BINARY : arch -> binOp -> reg -> reg+imm -> instruction
  (**r Branch *)
  | BPF_JA   : off -> instruction
  | BPF_JUMP : cond -> reg -> reg+imm -> off -> instruction

  (**r Load *)
  | BPF_LDDW_low : reg -> imm -> instruction
  | BPF_LDDW_high : reg -> imm -> instruction
  (**r Load_x *)
  | BPF_LDX  : memory_chunk -> reg -> reg -> off -> instruction
  (**r Store/ Store_x *)
  | BPF_ST   : memory_chunk -> reg -> reg+imm -> off -> instruction
  (**r exit *)
  | BPF_CALL : imm -> instruction
  | BPF_RET  : instruction
  | BPF_ERR  : instruction
.

Definition sum_eqb {A B: Type} (eq1 : A -> A -> bool) (eq2 : B -> B -> bool) (x y : sum A B) : bool :=
  match x, y with
  | inl r0', inl r1' => eq1  r0' r1'
  | inr i0', inr i1' => eq2  i0' i1'
  | _, _ => false
  end.


Definition bpf_instruction_eqb (a b: instruction) : bool :=
  match a, b with
  | BPF_NEG a0 r0, BPF_NEG a1 r1 => arch_eqb a0 a1 && reg_eqb r0 r1
  | BPF_BINARY a0 b0 r0 ri0, BPF_BINARY a1 b1 r1 ri1 => arch_eqb a0 a1 && binOp_eqb b0 b1 && reg_eqb r0 r1 && sum_eqb reg_eqb Int.eq ri0 ri1
  | BPF_JA ofs0, BPF_JA ofs1 => Int.eq ofs0 ofs1
  | BPF_JUMP c0 r0 ri0 ofs0, BPF_JUMP c1 r1 ri1 ofs1 => cond_eqb c0 c1 && reg_eqb r0 r1 && sum_eqb reg_eqb Int.eq ri0 ri1  && Int.eq ofs0 ofs1
  | BPF_LDDW_low r0 i0, BPF_LDDW_low r1 i1 => reg_eqb r0 r1 && Int.eq i0 i1
  | BPF_LDDW_high r0 i0, BPF_LDDW_high r1 i1 => reg_eqb r0 r1 && Int.eq i0 i1
  | BPF_LDX mc0 d0 s0 ofs0, BPF_LDX mc1 d1 s1 ofs1 => chunk_eqb mc0 mc1 && reg_eqb d0 d1 && reg_eqb s0 s1 && Int.eq ofs0 ofs1
  | BPF_ST mc0 r0 ri0 ofs0, BPF_ST mc1 r1 ri1 ofs1 => chunk_eqb mc0 mc1 && reg_eqb r0 r1 && sum_eqb reg_eqb Int.eq ri0 ri1 && Int.eq ofs0 ofs1
  | BPF_CALL i0 , BPF_CALL i1 => Int.eq i0 i1
  | BPF_RET, BPF_RET
  | BPF_ERR, BPF_ERR => true
  | _, _ => false
  end.

Lemma Int_eq_true:
  forall x y : int, Int.eq x y = true <-> x = y.
Proof.
  split.
  apply Int.same_if_eq.
  intro H; rewrite H; apply Int.eq_true.
Qed.

Lemma Int_eq_false:
  forall x y : int, Int.eq x y = false <-> x <> y.
Proof.
  split.
  intro H.
  assert (Hspec: if Int.eq x y then x = y else x <> y) by apply Int.eq_spec.
  rewrite H in Hspec.
  assumption.
  apply Int.eq_false.
Qed.

Lemma sum_eqb_true :
  forall {A B: Type} eq1 eq2
         (eq1_ok : forall x y, x = y <-> eq1 x y  = true)
         (eq2_ok : forall x y, x = y <-> eq2 x y  = true)
    (x y: sum A B),
  x = y <-> sum_eqb eq1 eq2 x y = true.
Proof.
  destruct x,y; simpl.
  - rewrite <- eq1_ok.
    intuition congruence.
  - intuition congruence.
  - intuition congruence.
  - rewrite <- eq2_ok.
    intuition congruence.
Qed.

Lemma bpf_instruction_eqb_true:
  forall x y, x = y <-> bpf_instruction_eqb x y = true.
Proof.
  unfold bpf_instruction_eqb.
  destruct x, y; try intuition congruence.
  - rewrite Bool.andb_true_iff.
    rewrite <- arch_eqb_true.
    rewrite <- reg_eqb_true.
    intuition congruence.
  - rewrite ! Bool.andb_true_iff.
    rewrite <- arch_eqb_true.
    rewrite <- reg_eqb_true.
    rewrite <- sum_eqb_true.
    rewrite <- binOp_eqb_true.
    intuition congruence.
    apply reg_eqb_true.
    intros. rewrite Int_eq_true.
    tauto.
  - rewrite Int_eq_true. intuition congruence.
  - rewrite! Bool.andb_true_iff.
    rewrite <- cond_eqb_true.
    rewrite <- sum_eqb_true.
    rewrite Int_eq_true.
    rewrite <- reg_eqb_true.
    intuition congruence.
    apply reg_eqb_true.
    intros. rewrite Int_eq_true.
    tauto.
  - rewrite! Bool.andb_true_iff.
    rewrite <- reg_eqb_true.
    rewrite Int_eq_true.
    intuition congruence.
  - rewrite! Bool.andb_true_iff.
    rewrite <- reg_eqb_true.
    rewrite Int_eq_true.
    intuition congruence.
  - rewrite! Bool.andb_true_iff.
    rewrite <- !reg_eqb_true.
    rewrite Int_eq_true.
    rewrite <- chunk_eqb_true.
    intuition congruence.
  - rewrite! Bool.andb_true_iff.
    rewrite <- chunk_eqb_true.
    rewrite <- reg_eqb_true.
    rewrite <- sum_eqb_true.
    rewrite Int_eq_true.
    intuition congruence.
    apply reg_eqb_true.
    intros. rewrite Int_eq_true.
    tauto.
  -     intros. rewrite Int_eq_true.
        intuition congruence.
Qed.

Lemma bpf_instruction_eqb_false:
  forall x y, x <> y <-> bpf_instruction_eqb x y = false.
Proof.
  intros.
  generalize (bpf_instruction_eqb_true x y).
  destruct (bpf_instruction_eqb x y); intuition congruence.
Qed.
