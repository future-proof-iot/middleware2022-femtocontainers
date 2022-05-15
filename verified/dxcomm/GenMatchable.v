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

(** Provide a simpler way to construct a Matchable type
    - the inductive type needs to be a simple enumeration type
    - the match is compiled into a switch

    The difficulty is that the [matchInterp] field of the MatchableType record is dependently typed.
    The good news is that, this is almost the type of the eliminator.
**)

From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

(** [switch_list [z1;...;zn] generates the body of a switch statement
    fun [e1;....;en;def] => (z1: e1) ; (z2:e2) ; .... ; (zn: en) *)
Fixpoint switch_list (l:list Z)  : list Csyntax.statement -> Result Csyntax.labeled_statements :=
  match l with
  | nil => (fun cases => match cases with
                         | do_def :: nil =>
                           Ok (Csyntax.LScons None do_def
                                           Csyntax.LSnil)
                         |   _     => Err MatchEncodingFailed
                         end)

  | e::l' => (fun cases =>
              match cases with
              | nil => Err MatchEncodingFailed
              | c1:: cases =>
                match switch_list l' cases with
                | Err x => Err x
                | Ok lcase  => Ok (Csyntax.LScons (Some e) c1 lcase)
                end
              end)
end.

(* [fold_type [x1;...;xn] A]  returns x1 -> ... -> xn -> A *)
Definition fold_type (l: list Type) (A: Type) :=
  fold_right (fun X Y : Type => X -> Y) A l.

(* last_arg_first A B [x1 ; ...; xn] (f : x1 -> .... -> xn -> A -> B) returns
   the function A -> x1 -> ... -> xn -> B *)

Fixpoint last_arg_first  (l: list Type) (A B:Type)
                           (f : fold_type l (A -> B)) :
  A -> fold_type l B :=
  match  l as l0  return fold_type l0 (A -> B) -> A -> fold_type l0 B
  with
  | [] => fun f0 => f0
  | T :: l0 =>
      fun f0 (x : A) (a1 : T) => last_arg_first l0 A B (f0 a1) x
  end f.

(* [listn v n] returns n copies of v i.e. [v;...;v] *)
Fixpoint listn {A: Type} (v:A) (n:nat) :=
  match n with
  | O => nil
  | S n => v :: listn v n
  end.

(** [mkEnumMatchableType t eq l def elim] returns a MatchableType for (coqType t) where
    - [eqb] is the equality test for (coqType t)
    - [l] returns for each element of the enumeration the value for the switch
    - [def] is the element of the enumeration used for the default case of the switch
    - [elim] is almost the recursor for the (coqType t)
 *)

Definition mkEnumMatchableType (t: CompilableType)
           (eqb : coqType t -> coqType t -> bool) (l: list (coqType t * Z)) (def : coqType t)
           (elim : forall (m : Monad) (A : Type),
               fold_right (fun X Y : Type => X -> Y) (coqType t -> (m A))
                          (map (fold_right (fun X Y : Type => X -> Y) (m A))
                               (map (map coqType) (listn [] (S (length l))))))   : MatchableType :=
  {| compilableType := t;
     encodeMatch  := (let cases := switch_list (List.map snd l) in
                      fun x lcases =>
                        match cases lcases with
                        | Err x => Err x
                        | Ok l'  => Ok (Csyntax.Sswitch x l')
                        end);
            matchProjectors  := listn [] (S (List.length l));
            matchInterpTypes := listn [] (S (List.length l));
            matchInterp :=  fun (m : Monad) (A : Type) (X : coqType t) =>
                              last_arg_first
                                (map (fold_right (fun X0 Y : Type => X0 -> Y) (m A))
                                     (map (map coqType) (listn [] (S (length l)))))
                                (coqType t) (m A) (elim m A) X
  |}.

Inductive enum := A | B | C.

Definition enumCompilableType := {| coqType := enum ; cType := Ctypes.Tint Ctypes.I16 Ctypes.Unsigned Ctypes.noattr |}.

Definition enum_eqb (x y: enum) : bool :=
  match x , y with
  | A , A => true
  | B , B => true
  | C , C => true
  | _, _  => false
  end.

Definition enumMatchableType : MatchableType :=
  Eval compute in
  mkEnumMatchableType  enumCompilableType enum_eqb
                       ((A, 0x10%Z) ::(B,0x50%Z) ::nil) C (fun m x => enum_rect (fun _ => m x)).
