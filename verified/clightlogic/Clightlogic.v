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

(** Structure of soundness proofs for dx generated programs *)
From Coq Require Import List.
From Coq Require Import Program.Equality.
From dx Require Import IR.
From compcert Require Import Coqlib Values.
From compcert Require Import SimplExpr.
From compcert Require Import Clight Globalenvs.

From bpf.comm Require Import Monad.
From compcert Require Import Integers.
From compcert Require Import Memory.
From compcert Require Import Smallstep.
From compcert Require Import Clightdefs.
Import Clightdefs.ClightNotations.

From bpf.clightlogic Require Import clight_exec.
Open Scope type_scope.

Ltac split_and :=
repeat match goal with
| |- ?A /\ ?B => split
end.

Definition without_mem {A B : Type} (P : A -> B -> Prop)
           (a : A) (b: B) (m: Memory.Mem.mem) :=  P a b.

Definition stateless {A B St : Type} (P : A -> B -> Prop)
           (a : A) (b: B) (st: St) (m: Memory.Mem.mem) :=  P a b.


Definition match_bool (b:bool) (v:val) :=
  v = Vint (if b then Integers.Int.one else Integers.Int.zero).

Definition inclb {A: Type} (eqb : A -> A -> bool) (l1 l2: list A) : bool :=
  List.forallb (fun x =>  List.existsb (eqb x) l2) l1.

Lemma inclb_incl :
  forall A (eqb: A -> A -> bool)
         (EQ : forall x y, eqb x y = true <-> x = y)
         l1 l2,
    inclb eqb l1 l2 = true <-> incl l1 l2.
Proof.
  unfold incl.
  induction l1; simpl.
  - tauto.
  - intros.
    rewrite andb_true_iff.
    rewrite IHl1.
    rewrite existsb_exists.
    split.
    + intros ((x & INx & EQB) & IN).
      rewrite EQ in EQB. subst.
      intros. destruct H. congruence.
      apply IN;auto.
    + intros.
      split ; auto.
      exists a. rewrite EQ.
      intuition.
Qed.

Definition union {A: Type} (eqb:A -> A -> bool) (l1 l2: list A) : list A :=
  l1 ++ (List.filter (fun x => negb (List.existsb (eqb x) l1)) l2).

Lemma union_incl :
  forall {A: Type} (eqb:A -> A -> bool)
         (EQ : forall x y, eqb x y = true <-> x = y)
         (l1 l2: list A),
    incl l1 (union eqb l1 l2)  /\ incl l2 (union eqb l1 l2).
Proof.
  unfold union,incl.
  split ; intros.
  - rewrite in_app_iff.
    tauto.
  - rewrite in_app_iff.
    rewrite filter_In.
    rewrite negb_true_iff.
    assert (eq_dec : forall (x y: A), {x = y} + { x<> y}).
    {
      intros.
      destruct (eqb x y) eqn:E.
      left. rewrite <- EQ. auto.
      right. intro.
      rewrite <- EQ in H0; congruence.
    }
    destruct (In_dec eq_dec a l1).
    tauto.
    right ; auto.
    split ; auto.
    destruct (existsb (eqb a) l1) eqn:E.
    rewrite existsb_exists in E.
    destruct E as (x & IN & EQx).
    rewrite EQ in EQx. intuition congruence.
    reflexivity.
Qed.

Lemma union_nil : forall {A: Type} eqb (l: list A),
    union eqb nil l = l.
Proof.
  unfold union.
  intros.
  simpl.
  induction l ; simpl; auto.
  congruence.
Qed.


(** dx requires primitives.
    For each primitive,
    we have soundness theorem relating the Coq function and the primitive expression.
    The primitive declaration is untyped.
*)

Fixpoint arrow_type (l : list Type) (r : Type) :=
  match l with
  |  nil => r
  | cons e l => e -> (arrow_type l r)
  end.

Fixpoint arrow_n (n:nat) (e : Type) (r: Type) :=
  match n with
  |  O => r
  | S n => e -> (arrow_n n e r)
  end.

Fixpoint rep {A: Type} (n:nat) (e: A) :=
  match n with
  | O => nil
  | S n => e :: (rep n e)
  end.


Lemma nil_not_cons : forall {A: Type} (e:A) (l:list A),
    nil = e :: l -> False.
Proof.
  intros. discriminate.
Defined.

Lemma car_eq : forall {A: Type} (e1 e2: A) l1 l2,
                      e1 :: l1 = e2 :: l2 -> e1 = e2.
Proof.
  intros. congruence.
Defined.

Lemma cdr_eq : forall {A: Type} (e1 e2: A) l1 l2,
                      e1 :: l1 = e2 :: l2 -> l1 = l2.
Proof.
  intros. congruence.
Defined.


Inductive dpair : Type :=
  mk {
      typ : Type;
      elt: typ
    }.

Module DList.
  Section A.
    Context {A: Type}.
    Variable F:  A -> Type.

    Inductive t : list A -> Type :=
    | DNil : t nil
    | DCons : forall {e:A} (v: F e) {l:list A} (dl:t l),
        t (e::l).

    Definition car {e: A} {l: list A} (dl : t  (e::l)) : F e.
      refine(
      match dl in (t l0) return match l0 with nil => nil = e::l  -> False | e :: l => F e end with
      | DNil => _
      | DCons e0 v l0 _ => _
      end).
      apply nil_not_cons.
      apply v.
    Defined.

    Definition cdr {e: A} {l: list A} (dl : t  (e::l)) : t l.
      refine (match dl in (t l0) return match l0 with nil => (nil = e :: l -> False) | e :: l => t l end with
      | DNil => _
      | DCons e0 _ l0 dl0 => dl0
      end).
      apply nil_not_cons.
    Defined.

    Fixpoint map_id (l: list A) (dl : t l) : t l.
      destruct l.
      - apply DNil.
      - destruct dl.
        exact DNil.
        apply (DCons v dl).
    Defined.


    Lemma Dnil_nil  : forall (dl: t nil), dl = DNil.
    Proof.
      intro.
      dependent destruction dl.
      reflexivity.
    Qed.


    Lemma map_id_id : forall l (dl:t l),
        dl = map_id l dl.
    Proof.
      induction l.
      simpl. apply Dnil_nil.
      simpl. intros. destruct dl; reflexivity.
    Qed.

    Lemma car_cdr : forall e l (dl : t (e::l)),
        dl = DCons (car dl) (cdr dl).
    Proof.
      dependent destruction dl.
      reflexivity.
    Qed.


  End A.

  Section FROMDP.

    Fixpoint of_list_dp (l : list dpair) : DList.t (fun x => x) (List.map typ l) :=
      match l as l' return DList.t (fun x => x) (List.map typ l') with
      | nil => DNil _
      |  (mk t v) :: l => DList.DCons (fun x => x) v (of_list_dp l)
      end.
  End FROMDP.

  Section FORALL.
    Context {A: Type}.
    Context {F : A -> Type}.
    Variable R : forall (a:A), F a -> Prop.

    Fixpoint Forall {l:list A} (dl1 : t F l) : Prop:=
        match dl1  with
        | @DNil _ _ => True
        | @DCons _ _ e v l0 dl2 =>
            R e v  /\ Forall  dl2
        end.
  End FORALL.

  Section FORALL2.
    Context {A: Type}.
    Context {F : A -> Type}.
    Context {G : A -> Type}.
    Variable R : forall (a:A), F a -> G a -> Prop.

    Fixpoint Forall2 {l:list A} (dl1 : t F l) :  forall (dl2 : t G l) , Prop:=
        match dl1 in (t _ l0) return (t G l0 -> Prop) with
        | @DNil _ _ => fun _  => True
        | @DCons _ _ e v l0 dl2 =>
          fun dl3  =>
            R e v (car G dl3) /\ Forall2  dl2 (cdr G dl3)
        end.

    Lemma Forall2_rew : forall (e:A) (e1:F e) (e2 : G e)
                               l (dl1 : t F l) (dl2 : t G l),
        @Forall2 (e::l) (@DCons _ _ e e1 l dl1) (@DCons _ _ e e2 l dl2) =
          (R e e1 e2 /\ @Forall2 l dl1 dl2).
    Proof.
      reflexivity.
    Qed.

    
  End FORALL2.


  Section ZIP.
    Context {A : Type}.
    Context {F : A -> Type}.
    Context {G : A -> Type}.

    Fixpoint zip {l:list A} (dl1 : t F l): forall (dl2 : t G l) , t (fun x => F x * G x)%type l:=
  match dl1 in (t _ l0) return (t G l0 -> t (fun x : A => F x * G x)%type l0) with
  | @DNil _ _ => fun _  => DNil (fun x : A => F x * G x)%type
  | @DCons _ _ e v l0 dl2 =>
      fun dl3 : t G (e :: l0) =>
        DCons (fun x : A => F x * G x)%type (v, car G dl3) (zip dl2 (cdr G dl3))
  end.

    End ZIP.


  Section MAP.
    Context {A: Type}.
    Context {F : A -> Type}.
    Context {G : A -> Type}.
    Variable M : forall (a:A), F a -> G a.

    Fixpoint Map {l:list A} (dl1 : t F l) : t G l :=
      match dl1 in (t _ l0) return t G l0 with
      | @DNil _ _ => DNil G
      | @DCons _ _ e v l0 dl2 =>
        DCons G  (M e v )  (Map dl2)
      end.
  End MAP.

  Section MAPT.
    Context {A B: Type}.
    Context {F : A -> Type}.
    Context {G : B -> Type}.
    Context (Ml : A -> B).
    Variable M : forall (a:A), F a -> G (Ml a).

    Fixpoint MapT {l:list A} (dl1 : t F l) : t G (map Ml l):=
      match dl1 in (t _ l0) return (t G (map Ml l0)) with
      | @DNil _ _ => DNil G
      | @DCons _ _ e v l0 dl2 =>
        DCons G  (M e v)
               (MapT  dl2)
      end.
  End MAPT.



  Section MAP2.
    Context {A: Type}.
    Context {F : A -> Type}.
    Context {G : A -> Type}.
    Context {H : A -> Type}.
    Variable M : forall (a:A), F a -> G a -> H a.

    Fixpoint map2 {l:list A} (dl1 : t F l) : t G l -> t H l:=
      match dl1 in (t _ l0) return (t G l0 -> t H l0) with
      | @DNil _ _ => fun _  => DNil H
      | @DCons _ _ e v l0 dl2 =>
      fun dl3  =>
        DCons H  (M e v (car G dl3))  (map2  dl2 (cdr G dl3))
      end.

  End MAP2.

  Section LIST.

    Context {A B: Type}.
    Context {F : A -> Type}.
    Variable G : forall (x:A), F x -> B.

    Fixpoint to_list {l:list A} (dl: t F l) : list B :=
      match dl with
      | DNil => nil
      | DCons e v l dl' => G e v :: (to_list  dl')
      end.

    Lemma length_to_list : forall l (dl: t F l),
        length (to_list dl) = length l.
    Proof.
      induction dl;simpl;auto.
    Qed.

  End LIST.

  Section OFLIST.

    Context {A B: Type}.

    Fixpoint of_list (l:list A) : t (fun (x:A) => A) l:=
      match l with
      | nil => DNil _
      | e::l => DCons _ e  (of_list l)
      end.

    Lemma length_nil_cons : forall {E: Type} (e: E) (l:list E) (r:Type),
        List.length (A:= E) nil = List.length (e :: l) -> r.
    Proof.
      discriminate.
    Qed.

    Lemma length_cons_cons : forall [E1 E2: Type] [e1:E1] [e2: E2] [l1:list E1] [l2: list E2],
        List.length (e1 :: l1) = List.length (e2 :: l2) ->
        Datatypes.length l1 = Datatypes.length l2.
    Proof.
      simpl. congruence.
    Qed.

    Fixpoint of_list_sl (l: list A)  (l' : list B) : forall (LEN : List.length l = List.length l'), t (fun (x:B) => A) l':=
      match l as l0 return (Datatypes.length l0 = Datatypes.length l' -> t (fun _ : B => A) l') with
      | nil =>
          match l'  with
          | nil => fun _  => DNil (fun _ : B => A)
          | b :: l'0 => @length_nil_cons B _ _ _
          end
      | a :: l0 =>
          match l'  with
          | nil => fun _ => DNil (fun _ : B => A)
          | b :: l'0 =>
              fun LEN1  => DCons (fun _ : B => A) a (of_list_sl l0 l'0 (length_cons_cons LEN1))
          end
      end.

    Lemma to_list_of_list_sl  : forall (l: list A) (l': list B) (LEN : List.length l = List.length l'),
        l = to_list (fun (_:B) (x:A) => x) (of_list_sl l l' LEN).
    Proof.
      induction l.
      - simpl. destruct l'.
        + simpl. reflexivity.
        + simpl. discriminate.
      - simpl.
        destruct l'.
        discriminate.
        simpl. intros.
        f_equal. apply IHl.
    Qed.

  End OFLIST.

  End DList.

Arguments  DList.DCons {A} {F} {e} v {l} dl.


Module MatchCType.
  Section S.
    Variable T : CompilableType.

    Record t  : Type := mk
      {
      rel : coqType T -> val -> Prop
      }.

  End S.


  Definition from_option (T : option CompilableType) :=
    match T with
    | None => unit
    | Some C => t C
    end.
End MatchCType.

Fixpoint cl_app {l : list Type} {r: Type} (f : arrow_type l r) (a : DList.t (fun x => x) l) : r:=
  match a in (DList.t _ l0) return (arrow_type l0 r -> r) with
  | @DList.DNil _ _ => fun f0 : arrow_type nil r => f0
  | @DList.DCons _ _ e v _ a' =>
      fun f => cl_app  (f v) a'
  end f.

Fixpoint app_n {e: Type} {r:Type} (d:e) (n: nat) (f: arrow_n n e r) (l:list e) {struct n} : r:=
  match n as n0 return (arrow_n n0 e r -> r) with
  | O => fun f0  => f0
  | S n0 =>
      fun f0  =>
      match l return r with
      | nil => @app_n e r d n0 (f0 d) (@nil e)
      | cons e0 l0 => @app_n e r d n0 (f0 e0) l0
      end
  end f.

Ltac car_cdr :=
  repeat match goal with
  | DL : @DList.t ?T _ (?E :: ?L) |- _ =>
    rewrite (@DList.car_cdr T _ E L DL) in *;
    let c := fresh "c" in
    let d := fresh "d" in
    set (c:= @DList.car _ _ _ _ DL) in *;
    set (d:= @DList.cdr _ _ _ _ DL)  in *;
    clearbody c; clearbody d ; clear DL
  | DL : DList.t _ nil |- _ =>
    rewrite (DList.Dnil_nil _ DL) in *; clear DL
         end.

Inductive modifies_spec :=
| ModNothing (* Same memory *)
| ModSomething (* Arbitrary modification *).

Definition incl_modifies (m1 m2 : modifies_spec) :=
match m1, m2 with
| ModNothing , _  | _ , ModSomething => True
| _ , ModNothing  => False
end.

Definition lub_modifies (m1 m2: modifies_spec) :=
match m1 , m2 with
| ModNothing , x | x , ModNothing => x
| ModSomething , _  => ModSomething
end.

Lemma incl_lub_left : forall m1 m2,
incl_modifies m1 (lub_modifies m1 m2).
Proof.
 destruct m1,m2; simpl; auto.
Qed.

Lemma incl_lub_right : forall m1 m2,
incl_modifies m2 (lub_modifies m1 m2).
Proof.
 destruct m1,m2; simpl; auto.
Qed.

Definition unmodifies_effect {St: Type} (md : modifies_spec) (m m' : Memory.Mem.mem) (st: St) (st': St) : Prop :=
  match md with
   | ModNothing => m = m' /\ st = st'
  | ModSomething => True
end.

Lemma unmodifies_effect_refl : forall {St:Type} mods m (st:St),
  unmodifies_effect mods m m st st.
Proof.
unfold unmodifies_effect.
destruct mods; auto.
Qed.


Lemma unmodifies_effect_mono : forall {St:Type} mods mods' m m' (st st': St)
  (INCL : incl_modifies mods' mods)
  (UN : unmodifies_effect mods' m m' st st'),
  unmodifies_effect mods m m' st st'.
Proof.
 intros.
 destruct mods'.
 - simpl in UN. destruct UN. subst.
   apply unmodifies_effect_refl.
 - destruct mods ; simpl in *; try tauto.
Qed.

Lemma unmodifies_effect_trans : forall {St:Type} l m1 m2 m3 (st1 st2 st3: St),
    unmodifies_effect l m1 m2 st1 st2 ->
    unmodifies_effect l m2 m3 st2 st3->
    unmodifies_effect l m1 m3 st1 st3.
Proof.
  unfold unmodifies_effect.
  intros.
  destruct l. intuition congruence.
  auto.
Qed.


Inductive Inv (St:Type) :=
| StateLess (SL : val -> Prop) : Inv St
| StateFull (SF : val -> St -> Memory.Mem.mem -> Prop) : Inv St.

Definition is_stateless {St:Type} (i : Inv St) :=
match i with
| StateLess _ => true
| StateFull _ => false
end.

Definition eval_inv {St: Type} (i : Inv St) (v: val) (st: St) (m: Memory.Mem.mem) :=
match i with
| StateLess sl => sl v
| StateFull sf => sf v st m
end.


Definition all_args (l : list Type) (is_pure: bool) :=
  if is_pure then l else (unit:Type) :: l.

Definition all_args_list (l : list Type) (is_pure : bool) (dl :DList.t (fun x => x) l) : DList.t (fun x => x) (all_args l is_pure) :=
  if is_pure as b return (DList.t (fun x : Type => x) (all_args l b))
  then dl
  else DList.DCons tt dl.



Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Variable args : list Type.
  Variable res : Type.

  (* [f] is a Coq Monadic function with the right type *)
  Variable f : arrow_type args (M St res).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn: Clight.function.

  Variable modifies : modifies_spec.

(*  Variable match_mem : Type -> val -> Memory.Mem.mem -> Prop.*)

  Variable is_pure : bool. (* [is_pure] is true iff the C function does not take the monadic state as argument. *)

  Variable match_state : St -> mem -> Prop.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Variable match_arg_list : DList.t (fun x => x -> Inv St) (all_args args is_pure).

  (* [match_res] relates the Coq result and the C result *)
  Variable match_res : res -> Inv St.

  Class correct_function (a: DList.t (fun x => x) args) :=
    mk_correct_function3
      {
        fn_eval_ok3 : forall (st:St),
          match cl_app (r:=M St res) f  a st with
          | None => True
          | Some (v',st') =>
              (* We prove that we can reach a return state *)
              forall (lval: DList.t (fun _ => val) (all_args  args is_pure)) k m
                (MS : match_state st m),
                (* they satisfy the pre-condition *)
                DList.Forall2 (fun (a:Type) (R: a -> Inv St) (X:a * val) => eval_inv (R (fst X)) (snd X) st m)
                              match_arg_list (DList.zip  (all_args_list args is_pure a ) lval) ->
                (* We prove that we can reach a return state *)
                Forall2 (fun v t => Cop.val_casted v (snd t)) (DList.to_list (fun _ v => v) lval) (fn_params fn) ->

                exists v m' t,
                Star (Clight.semantics2 p) (Callstate  (Ctypes.Internal fn)
                                                       (DList.to_list (fun x v => v) lval)  k m) t
                     (Returnstate v (call_cont k) m') /\
                  (* The return memory matches the return state *)
                  eval_inv (match_res  v') v st' m' /\ Cop.val_casted v (fn_return fn) /\
                  unmodifies_effect modifies m m' st st' /\
                  match_state st' m'
              end
      }.

End S.

Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Variable args : list Type.
  Variable res : Type.

  (* [f] is a Coq Monadic function with the right type *)
  Variable f : arrow_type args (M St res).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn: Clight.function.

  Variable modifies : modifies_spec.

(*  Variable match_mem : Type -> val -> Memory.Mem.mem -> Prop.*)

  Variable is_pure : bool. (* [is_pure] is true iff the C function does not take the monadic state as argument. *)

  Variable match_state : St -> mem -> Prop.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Variable match_arg_list : DList.t (fun x => x -> Inv St) (all_args args is_pure).
  Variable match_res : res -> Inv St.

  Lemma correct_function_strengthen :
    forall a,
    correct_function St p args res f fn ModNothing is_pure match_state match_arg_list match_res a ->
      correct_function St p args res f fn ModSomething is_pure match_state match_arg_list match_res a.
  Proof.
    constructor.
    intros. destruct H.
    specialize (fn_eval_ok4 st).
    destruct (cl_app f a st) ; auto.
    destruct p0; auto.
    intros.
    specialize (fn_eval_ok4  _ k _ MS H H0).
    destruct fn_eval_ok4 as (v & m' & t & ST & EI & VC & UM & MS').
    eexists. eexists. eexists.
    split_and; eauto.
    simpl in UM. destruct UM ; subst.
    apply unmodifies_effect_refl.
  Qed.

End S.

Definition apply_cont (k:cont) : option (statement * cont) :=
  match k with
  | Kstop => None
  | Kseq s k => Some(s,k)
  | Kloop1 s1 s2 k => Some (s2, Kloop2 s1 s2 k)
  | Kloop2 s1 s2 k => Some (Sloop s1 s2, k)
  | Kswitch k      => Some (Sskip,k)
  | Kcall _ _ _  _ _ => None
  end.


Section S.

  Variable St : Type.
  Variable p : Clight.program.

  Variable res : Type.
  Variable f : M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.
  Variable stm: Clight.statement.

  Variable modifies : modifies_spec.

  Variable match_arg : St -> temp_env -> Memory.Mem.mem -> Prop.

  Variable match_res : res -> St  -> temp_env -> Memory.Mem.mem -> Prop.

  Definition correct_statement (st : St) (le:temp_env) (m:Memory.Mem.mem) :=
    match_arg st le m ->
    match f  st with
    | None => True
    | Some (v',st') =>
        forall s' k k',
          apply_cont k = Some (s',k') ->
          exists le' m' t,
                  Star (Clight.semantics2 p) (State fn stm k empty_env le m) t
                       (State  fn s' k' empty_env le' m') /\
                    (* The return memory matches the return state *)
match_res v' st' le' m' /\ unmodifies_effect modifies m m' st st'
    end.

End S.


Definition match_elt {St: Type} (st: St) (m : Memory.Mem.mem) (le : temp_env)
           (r : (AST.ident * Ctypes.type) * Inv St) :=
  match Maps.PTree.get (fst (fst r)) le with
  | None => False
  | Some v => eval_inv (snd r) v st m /\ Cop.val_casted v (snd (fst r))
  end.

Definition match_temp_env {St: Type} (dl : list ((AST.ident * Ctypes.type) * Inv St))
           (le:temp_env) (st: St) (m : Memory.Mem.mem)
            : Prop :=
  Forall (match_elt st m le) dl.

Definition pre {St: Type} (ms : St -> mem -> Prop)
           (var_inv : list (positive * Ctypes.type * Inv St))
            (st: St) (le: temp_env)  (m: mem) :=
          ms st m /\  match_temp_env var_inv le st m.

Definition filter_inv {St: Type} (l : list (positive * Ctypes.type * Inv St)) :=
  List.filter (fun '((_,_),i) => is_stateless i) l.

Definition inv_of_modifies {St: Type} (m:modifies_spec) (l: list (positive * Ctypes.type * Inv St)) :=
match m with
| ModNothing => l
| ModSomething => filter_inv l
end.

Definition post {r St: Type} (modifies: modifies_spec)
           (ms : St -> mem -> Prop)
           (match_res : r -> Inv St)
           (var_inv : list (positive * Ctypes.type * Inv St))
           (vr : positive * Ctypes.type) (res : r)  (st:St) (le: temp_env) (m: Memory.Mem.mem) :=
    ms st m /\ match_temp_env ((vr, match_res res) :: inv_of_modifies modifies var_inv) le st m.

Definition post_unit {St: Type} (modifies: modifies_spec) (ms : St -> mem -> Prop) (match_res : unit -> Inv St)
           (var_inv : list (positive * Ctypes.type * Inv St))
           (r : unit) (st:St) (le: temp_env) (m: Memory.Mem.mem) :=
   ms st m /\ match_temp_env var_inv le st m /\ eval_inv (match_res r) Vundef st m.



Section S.

  Variable St : Type.
  Variable p : Clight.program.

  Variable res : Type.
  Variable f :  M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.
  Variable stm: Clight.statement.

  Variable modifies : modifies_spec.

  Variable match_state : St -> mem -> Prop.

  Variable match_arg : list ((AST.ident * Ctypes.type) * Inv St).

  Variable match_res : res -> Inv St.

  Definition correct_body (st : St) (le:temp_env) (m:Memory.Mem.mem) :=
    forall (MS : match_state st m),
    match_temp_env match_arg le st m ->
    match f st with
          | None => True
          | Some (v',st') =>
              (* We prove that we can reach a return state *)
              forall k,
                (* We prove that we can reach a return state *)
                exists v m' t,
                Star (Clight.semantics2 p) (State fn stm k empty_env le m)
                     t
                     (Returnstate v (call_cont k) m') /\
                  (* The return memory matches the return state *)
                  eval_inv (match_res v') v st' m' /\ Cop.val_casted v (fn_return fn) /\ match_state st' m' /\ unmodifies_effect modifies m m' st st'
          end.

End S.


Definition list_rel {St : Type} (args : list Type)
           (rargs : DList.t (fun x => x -> Inv St) args)
           (a     : DList.t (fun x => x) args) : list (Inv St) :=
  DList.to_list (fun (x : Type) H  => H)
             (DList.map2 (fun (a0 : Type) (F : a0 -> Inv St) x   => F x) rargs a).

Definition list_rel_arg {St : Type} (p : list (AST.ident * Ctypes.type)) (args : list Type)
(rargs : DList.t (fun x => x -> Inv St) args)
(a     : DList.t (fun x => x) args) :
list  (AST.ident * Ctypes.type * Inv St)
:=  List.combine p (list_rel args rargs a).


Lemma get_bind_parameter_temps_s :
  forall lp lv (i:AST.ident)  te,
    ~ In i (var_names lp) ->
    Maps.PTree.get i (bind_parameter_temps_s lp lv te) = Maps.PTree.get i te.
Proof.
  induction lp.
  - simpl. intros. reflexivity.
  - simpl.
    destruct a;simpl.
    intros. destruct lv. auto.
    destruct (Pos.eq_dec i i0).
    subst. tauto.
    rewrite IHlp.
    apply Maps.PTree.gso.
    congruence.
    tauto.
Qed.



Lemma match_arg_list_match_init_env :
  forall {St : Type} (targs: list Type)
         (lval: DList.t (fun _ => val) targs)
         (a   : DList.t (fun x => x) targs)
         (ma : DList.t (fun x => x -> Inv St) targs)
         m p te st
         (HLEN : length p = length targs)
         (NOREP1: Coqlib.list_norepet (var_names p))
         (MA : DList.Forall2 (fun (a : Type) (R : a -> Inv St) (X : a * val) => eval_inv (R (fst X)) (snd X) st m
                             ) ma (DList.zip a lval))
         (MA' : Forall2
                  (fun (v : val) (t : AST.ident * Ctypes.type) =>
                     Cop.val_casted v (snd t))
                  (DList.to_list (fun (_ : Type) (v : val) => v) lval) p)
  ,
      match_temp_env (list_rel_arg p targs ma a)
        (bind_parameter_temps_s p (DList.to_list (fun (_ : Type) (v0 : val) => v0) lval) te) st m .
Proof.
  unfold match_temp_env.
  induction targs.
  - intros. car_cdr.
    simpl.
    destruct p ; try discriminate.
    simpl. unfold list_rel_arg. simpl.
    constructor.
  - intros. car_cdr.
    destruct p ; try discriminate.
    simpl. destruct p.
    assert (NOTIN :~ In i (var_names p0)).
    {
      simpl in NOREP1.
      inv NOREP1. tauto.
    }
    unfold list_rel_arg.
    simpl.
    constructor.
    + unfold match_elt.
      simpl.
      rewrite get_bind_parameter_temps_s by assumption.
      rewrite Maps.PTree.gss.
      simpl in MA.
      inv MA'. simpl in H2.
      tauto.
    +
      eapply IHtargs.
      simpl in HLEN.
      congruence.
      inv NOREP1. auto.
      simpl in MA.
      tauto.
      inv MA';auto.
Qed.



Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Variable args : list Type.
  Variable res : Type.

  (* [f] is a Coq Monadic function with the right type *)
  Variable f : arrow_type args (M St res).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn: Clight.function.

  Variable modifies : modifies_spec.

  (* If [is_pure] is true, the C code has no handler to the monadic state *)
  Variable is_pure : bool.

  (* Usually, only the first arguments is using St.
     Most of the arguments do not use Memory.Mem.mem either *)
  Variable match_state : St -> mem -> Prop.

  Variable match_arg_list : DList.t (fun x => x -> Inv St) (all_args args is_pure).

  Variable match_res : res -> Inv St.


  Lemma correct_function_from_body : forall
      (DIS : Coqlib.list_disjoint (var_names (fn_params fn)) (var_names (fn_temps fn)))
      (NOREP1: Coqlib.list_norepet (var_names (fn_params fn)))
      (NOREP :  Coqlib.list_norepet (var_names (fn_vars fn)))
      (NOVAR : fn_vars fn = nil)
      (HLEN : Datatypes.length (fn_params fn) = Datatypes.length (all_args args is_pure))
      a
      (C : forall (st:St) le m, correct_body St p  res (cl_app f a) fn (fn_body fn) modifies match_state
                                          (list_rel_arg (fn_params fn) (all_args args is_pure) match_arg_list (all_args_list args is_pure  a))
                                          match_res st le m)

    ,
        correct_function St p args res f fn modifies is_pure match_state match_arg_list match_res a.
  Proof.
    econstructor.
    intros.
    destruct (cl_app f a st) eqn: EQ; auto.
    destruct p0 as (v',st').
    intros lval k m MS MM MA.
    specialize (C st (bind_parameter_temps_s (fn_params fn) ((DList.to_list (fun (_ : Type) (v0 : val) => v0) lval))
          (create_undef_temps (fn_temps fn))) m).
    unfold correct_body in C.
    rewrite EQ in C.
    exploit C;eauto.
    {
      apply match_arg_list_match_init_env;auto.
    }
    intros (v2& m'& t'& EX & RES).
    do 3 eexists.
    split_and; try tauto.
    -
    eapply star_step.
    econstructor ; eauto.
    econstructor ; eauto.
    rewrite NOVAR.
    econstructor ; eauto.
    rewrite bind_parameter_temps_eq.
    reflexivity.
    simpl.
    rewrite DList.length_to_list.
    auto.
    eapply star_trans.
    eauto.
    apply star_refl.
    reflexivity.
    reflexivity.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
Qed.


End S.




Lemma apply_cont_cont : forall p fn m k s' k' le,
    apply_cont k = Some (s', k') ->
    Step (semantics2 p)
         (State fn Sskip k empty_env le m) Events.E0
         (State fn s' k' empty_env le m).
Proof.
  intros.
  destruct k ; inversion H;subst.
  - econstructor ;eauto.
  - econstructor;eauto.
  - econstructor;eauto.
  - econstructor;eauto.
Qed.

Definition var_expr (e : expr) : option (AST.ident * Ctypes.type) :=
  match e with
  | Etempvar v t => Some(v,t)
  | Ecast (Etempvar v t) _ => Some (v, t)
  | _           => None
end.

Fixpoint map_opt {A B : Type} (F : A -> option B) (l : list A) : option (list B) :=
  match l with
  | nil => Some nil
  | e::l => match F e , map_opt F l with
            | Some v, Some l => Some (v::l)
            | _ , _ => None
            end
  end.

Lemma length_map_opt : forall {A B: Type} (F : A -> option B) (l : list A) l',
    map_opt F l = Some l' ->
    List.length l = List.length l'.
Proof.
  induction l; simpl.
  - intros. inv H. reflexivity.
  - intros. destruct (F a); try discriminate.
    destruct (map_opt F l) eqn:M; try discriminate.
    inv H.
    simpl. f_equal. apply IHl;auto.
Qed.



Lemma map_fst_combine : forall {A B: Type} (l1: list A) (l2: list B),
    List.length l1 = List.length l2 ->
    map fst (combine l1 l2) = l1.
Proof.
  induction l1; simpl.
  - reflexivity.
  - destruct l2; simpl.
    discriminate.
    intros.
    f_equal.
    auto.
Qed.

Lemma match_temp_env_cons :
  forall {St:Type} x te (st:St) m l,
         (match_elt st m te x) ->
         match_temp_env l te st m  ->
    match_temp_env (x::l) te st m.
Proof.
  unfold match_temp_env.
  constructor;auto.
Qed.


Lemma match_temp_env_set : forall {St:Type} x v te (st:St) m l
    (NOTIN: ~ In x (List.map (fun x => fst (fst x)) l)),
    match_temp_env l te st m ->
    match_temp_env l (Maps.PTree.set x v  te) st m.
Proof.
  unfold match_temp_env.
  induction l.
  - simpl. intros. constructor.
  - simpl. intros.
    inv H.
    constructor ; auto.
    unfold match_elt in H2.
    unfold match_elt.
    destruct (Pos.eq_dec (fst (fst a)) x).
   + subst.
     exfalso.
     apply NOTIN.
     left ; reflexivity.
   + rewrite Maps.PTree.gso by auto.
     auto.
Qed.

Lemma match_temp_env_up :
  forall {St:Type} te (st:St) m (st':St) m'  (l:list (AST.ident * Ctypes.type * Inv St))
         (MOD :
                forall x t r v,
                  In ((x,t),r) l ->
                  Maps.PTree.get x te = Some v ->
                  eval_inv r v st m -> eval_inv r v st' m')
  ,
    match_temp_env l te st m ->
    match_temp_env l te st' m'.
Proof.
  unfold match_temp_env.
  induction l.
  - constructor.
  - intros.
    inv H ; constructor ; auto.
    unfold match_elt in *.
    destruct (Maps.PTree.get (fst (fst a)) te) eqn:G;auto.
    destruct H2 ; split ; auto.
    destruct a as ((x,t),r).
    simpl in *.
    eapply MOD;eauto.
    eapply IHl;eauto.
    intros.
    eapply MOD ;eauto.
    simpl. right;eauto.
Qed.


Definition  exec_deref_loc (ty : Ctypes.type) (m : Memory.Mem.mem) (b : block) (ofs : ptrofs) : option val :=
  match Ctypes.access_mode ty with
  | Ctypes.By_value chk => Memory.Mem.loadv chk m (Vptr b ofs)
  | Ctypes.By_reference => Some (Vptr b ofs)
  | Ctypes.By_copy => Some (Vptr b ofs)
  | Ctypes.By_nothing => None
  end.


(**r ysh: executing clight expressions, return the result of the expression (Q: Clight has `eval_expr`, is a relation ), this definition should be equivalent to clight's `eval_expr` *)
Fixpoint exec_expr (ge:genv) (ev:env) (le: temp_env) (m:Memory.Mem.mem) (e: expr) {struct e} : option val :=
  match e with
  | Econst_int i t    => Some (Vint  i)
  | Econst_float f _  => Some (Vfloat f)
  | Econst_single f _ => Some (Vsingle f)
  | Econst_long  l _  => Some (Vlong l)
  | Evar v  t         => match Maps.PTree.get v ev with
                         | Some (b,t') => (**r ysh: local variable *)
                            if Ctypes.type_eq t t' then
                              exec_deref_loc t m b  Ptrofs.zero
                            else None
                         | None   => (**r ysh: global variable *)
                            match (Globalenvs.Genv.find_symbol ge v) with
                            | None => None
                            | Some b => exec_deref_loc t m b  Ptrofs.zero
                            end
                         end
  | Etempvar id t     => Maps.PTree.get id le
  | Ederef e t        => match exec_expr ge ev le m e with  (**r ysh: None -> *)
                         | None => None
                         | Some v => 
                            match v with
                            | Vptr b ofs => exec_deref_loc t m b ofs
                            | _ => None
                            end
                         end
  | Eaddrof _ _       => None
  | Eunop o e t       => match exec_expr ge ev le m e with
                         | None => None
                         | Some v => Cop.sem_unary_operation o v (typeof e) m
                         end
  | Ebinop o e1 e2 t    => match exec_expr ge ev le m e1 , exec_expr ge ev le m e2 with
                           | Some v1 , Some v2 => Cop.sem_binary_operation ge o v1 (typeof e1) v2 (typeof e2) m
                           | _ , _ => None
                           end
  | Ecast e ty        => match exec_expr ge ev le m e with
                         | None => None
                         | Some v => Cop.sem_cast v (typeof e) ty m
                         end
| Efield e i ty      => match exec_expr ge ev le m e with
                        | Some (Vptr l ofs) =>
                            match typeof e with
                              | Ctypes.Tstruct id _  =>
                                  match Maps.PTree.get id ge.(genv_cenv) with
                                  | Some co =>
                                      match Ctypes.field_offset ge i (Ctypes.co_members co) with
                                      | Errors.OK(delta) =>
                                          exec_deref_loc ty m l (Ptrofs.add ofs (Ptrofs.repr delta))
                                      |  _  => None
                                      end
                                  | _   => None
                                  end
                            |  _ => None
                            end
                        |  _ => None
                        end
  | Esizeof _ _       => None
  | Ealignof _ _      => None
  end.

Lemma deref_loc_var : forall t m b v ofs,
    exec_deref_loc t m b ofs = Some v -> (**r ysh: zero -> ofs *)
    deref_loc t m b ofs v.
Proof.
  intros.
  unfold exec_deref_loc in H.
  destruct (Ctypes.access_mode t) eqn:AM.
  eapply deref_loc_value; eauto.
  inv H. eapply deref_loc_reference; eauto.
  inv H. eapply deref_loc_copy; eauto.
  discriminate.
Qed.

(**r ysh: The Lemma tells the relation between `exec_expr` and Clight's `eval_expr` *)
Lemma eval_expr_eval : forall ge ev te m e v,
    exec_expr ge ev te m e = Some v ->
    eval_expr ge ev te m e v.
Proof.
  induction e.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros.
    destruct (Maps.PTree.get i ev) eqn:G.
    + destruct p.
      destruct (Ctypes.type_eq t t0).
      * subst.
        econstructor. eauto.
        econstructor.
        eauto.
        apply deref_loc_var. auto.
      * discriminate.
    +
      destruct (Globalenvs.Genv.find_symbol ge i) eqn:FS; try discriminate.
      simpl in H. inv H.
      econstructor.
      eapply eval_Evar_global;eauto.
      apply deref_loc_var. auto.
  - simpl. intros.
    econstructor ; eauto.
  - intros.
    simpl in H.
    destruct (exec_expr ge ev te m e) eqn: He; try discriminate.
    destruct v0 eqn: Hv0; try discriminate.
    subst.
    econstructor.
    econstructor. eauto.
    apply deref_loc_var. simpl. auto.
  - intros ; discriminate.
  - simpl.
    intros.
    destruct (exec_expr ge ev te m e) eqn:EE.
    econstructor.
    eauto. auto.
    discriminate.
  - intros.
    simpl in H.
    destruct (exec_expr ge ev te m e1) eqn:E1; try discriminate.
    destruct (exec_expr ge ev te m e2) eqn:E2; try discriminate.
    econstructor ; eauto.
  - intros.
    simpl in H.
    destruct (exec_expr ge ev te m e) eqn:E; try discriminate.
    inv H. econstructor.
    eauto. auto.
  - simpl. intros.
    destruct (exec_expr ge ev te m e) eqn:EX; try discriminate.
    destruct v0 ; try discriminate.
    specialize (IHe _ eq_refl).
    destruct (typeof e) eqn:TO ; try discriminate.
    destruct (@Maps.PTree.get Ctypes.composite i1 (genv_cenv ge)) eqn:GET ; try discriminate.
    destruct (Ctypes.field_offset ge i (Ctypes.co_members c)) eqn:OF; try discriminate.
    econstructor.
    econstructor; eauto.
    eapply deref_loc_var; auto.
  - discriminate.
  - discriminate.
Qed.

Definition is_Vint (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tint Ctypes.I32 si attr => true
  | Ctypes.Tpointer ty attr    => negb Archi.ptr64
  | Ctypes.Tvoid
  |   _  => false
  end.


Definition is_VBool (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tint Ctypes.IBool si attr => true
  |   _  => false
  end.

Lemma val_casted_is_VBool : forall b t,
    is_VBool t = true ->
    Cop.val_casted (Val.of_bool b) t.
Proof.
  destruct t ; try discriminate.
  simpl. destruct i; try discriminate.
  destruct b; constructor.
  reflexivity. reflexivity.
Qed.

Definition is_Vfloat (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tfloat Ctypes.F64 attr => true
  | Ctypes.Tvoid
  | _  => false
  end.

Definition is_Vsingle (t: Ctypes.type) : bool :=
  match t with
  |Ctypes.Tfloat Ctypes.F32 attr => true
  | Ctypes.Tvoid
  | _  => false
  end.

Definition is_Vlong (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tlong si attr  => true
  | Ctypes.Tpointer ty attr    => Archi.ptr64
  | Ctypes.Tvoid
  | _ => false
  end.

Definition is_Vptr (t : Ctypes.type) : bool :=
  match t with
  | Ctypes.Tpointer ty attr => true
  | Ctypes.Tlong si attr    => Archi.ptr64
  | Ctypes.Tint Ctypes.I32 si attr => negb Archi.ptr64
  | Ctypes.Tvoid => true
  | _    => false
  end.

Definition is_Vundef (t : Ctypes.type) : bool :=
  match t with
  | Ctypes.Tvoid => true
  | _    => false
  end.


Ltac discr_bool := match goal with
                   | H : false = true |- _ => discriminate H
                   end.


Lemma is_Vint_casted : forall i t,
    is_Vint t = true ->
    Cop.val_casted (Vint i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  destruct i0; try discr_bool.
  constructor. reflexivity.
  constructor.
  rewrite negb_true_iff in H.
  auto.
Qed.

Lemma is_Vfloat_casted : forall i t,
    is_Vfloat t = true ->
    Cop.val_casted (Vfloat i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  destruct f; try discr_bool.
  constructor.
Qed.


Lemma is_Vsingle_casted : forall i t,
    is_Vsingle t = true ->
    Cop.val_casted (Vsingle i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  destruct f; try discr_bool.
  constructor.
Qed.

Lemma is_Vlong_casted : forall i t,
    is_Vlong t = true ->
    Cop.val_casted (Vlong i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  constructor.
  constructor. auto.
Qed.

Lemma is_Vptr_casted : forall b o t,
    is_Vptr t = true ->
    Cop.val_casted (Vptr b o) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  constructor.
  destruct i; try discr_bool.
  constructor.   rewrite negb_true_iff in H.   auto.
  constructor;auto. constructor.
Qed.

Import Cop.

Inductive classify_op_cases := | OADD | OSUB | OSHIFT | OBOOL | OOTHER.

Definition classify_op (o:Cop.binary_operation) : classify_op_cases :=
  match o with
  | Oadd => OADD
  | Osub => OSUB
  | Oshl | Oshr => OSHIFT
  | Oeq | One | Olt | Ogt | Ole | Oge  => OBOOL
  | _ => OOTHER
  end.




Definition vc_binary_operation_casted (o: Cop.binary_operation) (t1 t2: Ctypes.type) (r :Ctypes.type): bool :=
  match o with
  | Oadd => match classify_add t1 t2 with
            | add_default => Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) r

            |  _          => false
            end
  | Osub => match classify_sub t1 t2 with
            | sub_default => Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) r

            |  _          => false
            end
  | Omul   | Odiv | Omod   | Oand
  | Oor | Oxor  =>
            (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1 &&
              Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2 &&
               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) r )
            || (Ctypes.type_eq t1 Clightdefs.tuchar  &&
                  Ctypes.type_eq t2 Clightdefs.tint &&
                  Ctypes.type_eq r Clightdefs.tint
               )
            || (Ctypes.type_eq t2 Clightdefs.tuchar &&
                  Ctypes.type_eq t1 Clightdefs.tint &&
                  Ctypes.type_eq r Clightdefs.tint
               )


  | Oshl | Oshr => match classify_shift t1 t2 with
                   | shift_case_ii _ => is_Vint r
                   | shift_case_ll _ => is_Vlong r
                   | shift_case_il  _ => is_Vint r
                   | shift_case_li _  => is_Vlong r
                   | shift_default     => false
                   end
  | Oeq | One | Olt | Ogt | Ole | Oge  => is_VBool r
  end.

(*
Definition classify_notint_eq (t1 t2:  classify_notint_cases) : bool :=
  match t1, t2 with
  | notint_case_i _ , notint_case_i _ => true
  | notint_case_l _ , notint_case_l _ => true
  | notint_default , notint_default   => true
  | _ , _ => false
  end.
*)

Definition vc_unary_operation_casted (o: Cop.unary_operation) (t1 : Ctypes.type) (r :Ctypes.type): bool :=
  match o with
  | Onotbool => is_VBool r
  | Onotint  => match classify_notint t1 with
                | notint_case_i s => is_Vint r
                | notint_case_l s => is_Vlong r
                | notint_default  => true
                end
  | Oneg     => match classify_neg t1 with
                | neg_case_i s => is_Vint r
                | neg_case_l s => is_Vlong r
                | neg_case_f   => is_Vfloat r
                | neg_case_s   => is_Vsingle r
                | neg_default  => true
                end
  | Oabsfloat => is_Vfloat r
  end.


Lemma vc_casted_unary_operation_correct : forall o v1 t1  t v m
    (VC : Cop.val_casted v1 t1)
    (UO : vc_unary_operation_casted o t1  t = true)
    (SO : Cop.sem_unary_operation o v1 t1 m = Some v),
  Cop.val_casted v t.
Proof.
  destruct o; simpl; intros.
  - unfold sem_notbool in SO.
    destruct (bool_val v1 t1 m) eqn:BV; try discriminate.
    simpl in SO.
    inv SO.
    apply val_casted_is_VBool.
    apply UO.
  - unfold sem_notint in SO.
    destruct (classify_notint t1) eqn:CT1.
    + destruct v1 ; try discriminate.
      inv SO.
      apply is_Vint_casted.
      apply UO.
    + destruct v1 ; try discriminate.
      inv SO.
      apply is_Vlong_casted.
      apply UO.
    + discriminate.
  - unfold sem_neg in SO.
    destruct (classify_neg t1) eqn:CN.
    + destruct v1 ; try discriminate.
      inv SO.
      apply is_Vint_casted.
      apply UO.
    + destruct v1 ; try discriminate.
      inv SO.
      apply is_Vfloat_casted.
      apply UO.
    + destruct v1 ; try discriminate.
      inv SO.
      apply is_Vsingle_casted.
      apply UO.
    + destruct v1 ; try discriminate.
      inv SO.
      apply is_Vlong_casted.
      apply UO.
    + discriminate.
  - unfold sem_absfloat in SO.
    destruct (classify_neg t1) eqn:CN; destruct v1 ; try discriminate.
    inv SO.
    apply is_Vfloat_casted; auto.
    inv SO.
    apply is_Vfloat_casted; auto.
    inv SO.
    apply is_Vfloat_casted; auto.
    inv SO.
    apply is_Vfloat_casted; auto.
Qed.



Definition var_casted_list (l: list (positive * Ctypes.type)) (le: temp_env) : Prop:=
  forall i t v,  In (i, t) l ->
               Maps.PTree.get i le = Some v ->
               Cop.val_casted v t.

Lemma val_casted_sem_binarith :
  forall f1 f2 f3 f4 v1 v2 t m v
         (BC : binarith_type (classify_binarith t t) = t)
         (SB : sem_binarith f1 f2 f3 f4 v1 t v2 t m = Some v)
         (WC1: forall s x y r,
             Ctypes.Tint Ctypes.I32 s Ctypes.noattr = t ->
             val_casted (Vint x) t ->
             val_casted (Vint y) t -> f1 s x y = Some r ->
             val_casted r t)
         (WC2: forall s x y r,
             Ctypes.Tlong s Ctypes.noattr = t ->
             val_casted (Vlong x) t ->
             val_casted (Vlong y) t -> f2 s x y = Some r ->
             val_casted r t)
         (WC3: forall x y r,
             Ctypes.Tfloat Ctypes.F64 Ctypes.noattr = t ->
             val_casted (Vfloat x) t ->
             val_casted (Vfloat y) t -> f3 x y = Some r ->
             val_casted r t)
         (WC4: forall x y r,
             Ctypes.Tfloat Ctypes.F32 Ctypes.noattr = t ->
             val_casted (Vsingle x) t ->
             val_casted (Vsingle y) t -> f4 x y = Some r ->
             val_casted r t),
    val_casted v1 t ->
    val_casted v2 t ->
    val_casted v t.
Proof.
  unfold sem_binarith.
  intros.
  rewrite BC in SB.
  rewrite! cast_val_casted in SB by auto.
  destruct (classify_binarith t t).
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC1 in SB; auto.
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC2 in SB;auto.
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC3 in SB; auto.
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC4 in SB; auto.
  - discriminate.
Qed.

Lemma val_casted_cmp_ptr : forall m c v1 v2 v t,
    is_VBool t = true ->
    cmp_ptr m c v1 v2 = Some v ->
  val_casted v t.
Proof.
  unfold cmp_ptr.
  intros.
  destruct Archi.ptr64.
  destruct (Val.cmplu_bool (Memory.Mem.valid_pointer m) c v1 v2); try discriminate.
  inv H0. apply val_casted_is_VBool; auto.
  destruct (Val.cmpu_bool (Memory.Mem.valid_pointer m) c v1 v2); try discriminate.
  inv H0. apply val_casted_is_VBool; auto.
Qed.

Lemma val_casted_sem_cmp :
  forall o (v1 : val) (t1 : Ctypes.type) (v2 : val) (t2 t : Ctypes.type) (v : val) (m : Memory.Mem.mem),
    val_casted v1 t1 -> val_casted v2 t2 -> is_VBool t = true -> sem_cmp o v1 t1 v2 t2 m = Some v -> val_casted v t.
Proof.
  unfold sem_cmp. intros.
  destruct Archi.ptr64.
  destruct (classify_cmp t1 t2);
    try (eapply val_casted_cmp_ptr;eauto;fail).
  destruct v2 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  destruct v1 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  destruct v2 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  destruct v1 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  unfold sem_binarith in H2.
  destruct (sem_cast v1 t1 (binarith_type (classify_binarith t1 t2)) m);
    destruct (sem_cast v2 t2 (binarith_type (classify_binarith t1 t2)) m);
    destruct (classify_binarith t1 t2); try discriminate.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct (classify_cmp t1 t2).
    eapply val_casted_cmp_ptr;eauto.
    destruct v2 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
    destruct v1 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
    destruct v2 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
    destruct v1 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
  unfold sem_binarith in H2.
  destruct (sem_cast v1 t1 (binarith_type (classify_binarith t1 t2)) m);
    destruct (sem_cast v2 t2 (binarith_type (classify_binarith t1 t2)) m);
    destruct (classify_binarith t1 t2); try discriminate.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
Qed.

Lemma vc_casted_binary_other_correct :
  forall  o v1 t1 v2 t2 t v m
          FVint FVlong FVfloat FVsingle
    (FVinCasted : forall (s : Ctypes.signedness) (x y : int) (r : val),
        Ctypes.Tint Ctypes.I32 s Ctypes.noattr = t ->
        val_casted (Vint x) t ->
        val_casted (Vint y) t -> FVint s x y = Some r -> val_casted r t)
    (FVlongCasted :
      forall (s : Ctypes.signedness) (x y : int64) (r : val),
        Ctypes.Tlong s Ctypes.noattr = t ->
        val_casted (Vlong x) t ->
        val_casted (Vlong y) t -> FVlong s x y = Some r -> val_casted r t)
    (FVfloatCasted : forall (x y : Floats.float) (r : val),
        Ctypes.Tfloat Ctypes.F64 Ctypes.noattr = t ->
        val_casted (Vfloat x) t ->
        val_casted (Vfloat y) t -> FVfloat x y = Some r -> val_casted r t)
    (FCsingleCasted :
      forall (x y : Floats.float32) (r : val),
        Ctypes.Tfloat Ctypes.F32 Ctypes.noattr = t ->
        val_casted (Vsingle x) t ->
        val_casted (Vsingle y) t -> FVsingle x y = Some r -> val_casted r t)
    (CV1 : val_casted v1 t1)
    (CV2 : val_casted v2 t2)
    (VC : Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1 &&
            Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2 &&
            Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t
          || Ctypes.type_eq t1 tuchar && Ctypes.type_eq t2 tint &&
               Ctypes.type_eq t tint
          || Ctypes.type_eq t2 tuchar && Ctypes.type_eq t1 tint &&
               Ctypes.type_eq t tint = true)
    (B : sem_binarith
           FVint
           FVlong
           FVfloat
           FVsingle
           v1 t1 v2 t2 m = Some v)
    (CO : classify_op o = OOTHER),
    val_casted v t.
Proof.
  intros.
  rewrite! orb_true_iff in *.
  rewrite! andb_true_iff in *.
  destruct VC as [[VC1|VC1]|VC1].
  - destruct VC1 as ((VC1 & VC2) & VC3).
  destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H in *.
    assert (t2 = t) by congruence.
    rewrite H0 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
  - destruct VC1 as ((VC1& VC2) & VC3).
    destruct (Ctypes.type_eq t1 tuchar); try discriminate.
    destruct (Ctypes.type_eq t2 tint); try discriminate.
    destruct (Ctypes.type_eq t tint); try discriminate.
    subst.
    eapply val_casted_sem_binarith ;eauto.
    inv CV1.
    constructor.
    unfold cast_int_int in *.
    reflexivity.
  - destruct VC1 as ((VC1& VC2) & VC3).
    destruct (Ctypes.type_eq t2 tuchar); try discriminate.
    destruct (Ctypes.type_eq t1 tint); try discriminate.
    destruct (Ctypes.type_eq t tint); try discriminate.
    subst.
    eapply val_casted_sem_binarith ;eauto.
    inv CV2.
    constructor.
    unfold cast_int_int in *.
    reflexivity.
Qed.


Lemma vc_casted_binary_operation_correct :
  forall ge o v1 t1 v2 t2 t v m
         (CV1: Cop.val_casted v1 t1)
         (CV2: Cop.val_casted v2 t2)
         (VC :vc_binary_operation_casted o t1 t2 t = true)
         (B  : Cop.sem_binary_operation ge o v1 t1 v2 t2 m = Some v),
  Cop.val_casted v t.
Proof.
  intros.
  destruct (classify_op o) eqn:CO.
  - destruct o ; try discriminate.
    simpl in B.
    simpl in VC.
    unfold sem_add in B.
    destruct (classify_add t1 t2) eqn:CL; try congruence.
    rewrite! andb_true_iff in VC.
    destruct VC as ((VC1 & VC2) & VC3).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H in *.
    assert (t2 = t) by congruence.
    rewrite H0 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros.
      simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor. reflexivity.
    + intros. simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor.
    + intros. simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor.
    + intros. simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor.
  - destruct o ; try discriminate.
    simpl in B.
    simpl in VC.
    unfold sem_sub in B.
    destruct (classify_sub t1 t2) eqn:CL; try congruence.
    rewrite! andb_true_iff in VC.
    destruct VC as ((T1 & T2) & T3).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
      destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H in *.
    assert (t2 = t) by congruence.
    rewrite H0 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    +
      intros. simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor. reflexivity.
    + intros. simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor.
    + intros. simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor.
    + intros. simpl in H4. rewrite <- H1 in *.
      inv H4.
      constructor.
  - destruct o; try discriminate.
    { unfold vc_binary_operation_casted in VC.
      unfold sem_binary_operation in B.
      unfold sem_shl in *.
      unfold sem_shift in *.
      destruct (classify_shift t1 t2) eqn:CS.
      +
        destruct v1,v2 ; try discriminate.
        destruct (Int.ltu i0 Int.iwordsize); try discriminate.
        inv B. apply is_Vint_casted; auto.
      + destruct v1,v2 ; try discriminate.
        destruct (Int64.ltu i0 Int64.iwordsize); try discriminate.
        inv B. apply is_Vlong_casted; auto.
    + destruct v1,v2 ; try discriminate.
      destruct (Int64.ltu i0 (Int64.repr 32)); try discriminate.
      inv B. apply is_Vint_casted; auto.
    +  destruct v1,v2 ; try discriminate.
      destruct (Int.ltu i0 (Int64.iwordsize')); try discriminate.
      inv B. apply is_Vlong_casted; auto.
    +  discriminate.
    }
{ unfold vc_binary_operation_casted in VC.
      unfold sem_binary_operation in B.
      unfold sem_shr in *.
      unfold sem_shift in *.
      destruct (classify_shift t1 t2) eqn:CS.
      +
        destruct v1,v2 ; try discriminate.
        destruct (Int.ltu i0 Int.iwordsize); try discriminate.
        inv B. apply is_Vint_casted; auto.
      + destruct v1,v2 ; try discriminate.
        destruct (Int64.ltu i0 Int64.iwordsize); try discriminate.
        inv B. apply is_Vlong_casted; auto.
    + destruct v1,v2 ; try discriminate.
      destruct (Int64.ltu i0 (Int64.repr 32)); try discriminate.
      inv B. apply is_Vint_casted; auto.
    +  destruct v1,v2 ; try discriminate.
      destruct (Int.ltu i0 (Int64.iwordsize')); try discriminate.
      inv B. apply is_Vlong_casted; auto.
    +  discriminate.
    }
  -
    assert (exists c, sem_cmp c v1 t1 v2 t2 m = Some v).
    { unfold sem_binary_operation in B.
      destruct o ; try discriminate; eexists ; eauto.
    }
    destruct H.
    eapply val_casted_sem_cmp in H; eauto.
    unfold vc_binary_operation_casted in VC.
    destruct o ; try discriminate; auto.
  - unfold sem_binary_operation in B.
    destruct o; try discriminate.
    + unfold sem_mul in B.
      eapply vc_casted_binary_other_correct in B; eauto.
      intros. inv H2. constructor. reflexivity.
      intros. inv H2. constructor.
      intros. inv H2. constructor.
      intros. inv H2. constructor.
    + unfold sem_div in B.
      eapply vc_casted_binary_other_correct in B; eauto.
    *  intros.
      destruct s.
      destruct (Int.eq y Int.zero || Int.eq x (Int.repr Int.min_signed) && Int.eq y Int.mone); try congruence.
      inv H2. constructor. reflexivity.
      destruct (Int.eq y Int.zero) ; try congruence.
      inv H2. constructor. reflexivity.
    * intros.
      destruct s.
      destruct (Int64.eq y Int64.zero || Int64.eq x (Int64.repr Int64.min_signed) && Int64.eq y Int64.mone); try congruence.
      inv H2. constructor.
      destruct (Int64.eq y Int64.zero) ; try congruence.
      inv H2. constructor.
    * intros. inv H2. constructor.
    * intros. inv H2. constructor.
    + unfold sem_div in B.
      eapply vc_casted_binary_other_correct in B; eauto.
    *  intros.
      destruct s.
      destruct (Int.eq y Int.zero || Int.eq x (Int.repr Int.min_signed) && Int.eq y Int.mone); try congruence.
      inv H2. constructor. reflexivity.
      destruct (Int.eq y Int.zero) ; try congruence.
      inv H2. constructor. reflexivity.
    * intros.
      destruct s.
      destruct (Int64.eq y Int64.zero || Int64.eq x (Int64.repr Int64.min_signed) && Int64.eq y Int64.mone); try congruence.
      inv H2. constructor.
      destruct (Int64.eq y Int64.zero) ; try congruence.
      inv H2. constructor.
    * intros. discriminate.
    * intros. discriminate.
    + unfold sem_and in B.
      eapply vc_casted_binary_other_correct in B; eauto.
      intros. inv H2. constructor. reflexivity.
      intros. inv H2. constructor.
      intros. discriminate.
      intros. discriminate.
    + unfold sem_or in B.
      eapply vc_casted_binary_other_correct in B; eauto.
      intros. inv H2. constructor. reflexivity.
      intros. inv H2. constructor.
      intros. discriminate.
      intros. discriminate.
    + unfold sem_xor in B.
      eapply vc_casted_binary_other_correct in B; eauto.
      intros. inv H2. constructor. reflexivity.
      intros. inv H2. constructor.
      intros. discriminate.
      intros. discriminate.
Qed.

Definition vc_cast_casted (o:Ctypes.type) (d:Ctypes.type) :=
  match classify_cast o d with
  | cast_case_pointer => is_Vptr d
  | cast_case_i2l si  => true
  | cast_case_l2l     => true
  | cast_case_i2i sz s    => true
  | cast_case_l2i i s     => true
  |  _                 => false
  end.

Lemma val_casted_sem_cast : forall t1 t v v' m,
    vc_cast_casted t1 t = true ->
    sem_cast v t1 t m = Some v' ->
  val_casted v' t.
Proof.
  intros.
  unfold vc_cast_casted in H.
  unfold sem_cast in H0.
  destruct (classify_cast t1 t) eqn:CC; try discriminate.
  - destruct v ; try congruence.
    destruct Archi.ptr64 eqn:A; try congruence.
    inv H0.
    destruct t ; simpl in H ; try congruence.
    constructor. rewrite A in H.
    destruct i0; try congruence. constructor.
    reflexivity.
    constructor. auto.
    destruct Archi.ptr64 eqn:A; try congruence.
    inv H0.
    destruct t ; simpl in H ; try congruence.
    constructor. rewrite A in H.
    destruct i0; try congruence. discriminate H.
    constructor. constructor;auto.
    inv H0.
    eapply is_Vptr_casted; eauto.
  - destruct v; try discriminate.
    inv H0. unfold classify_cast in CC.
    repeat
    match goal with
    | H : context[match ?X with _ => _ end] |- _ => destruct X ; try discriminate
    end; try inv CC ; constructor; try apply cast_int_int_idem.
  - destruct v; try discriminate.
    inv H0.
    unfold classify_cast in CC.
    destruct t1; try discriminate.
    + destruct t; try discriminate.
      destruct i0; discriminate.
      destruct f; discriminate.
    + destruct t; try congruence.
      destruct i1;try congruence.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct f; discriminate.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      constructor.
      destruct f ; discriminate.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f0; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
    + destruct t ; try discriminate.
      destruct i0; try discriminate.
      destruct f ; try discriminate.
    + destruct t ; try discriminate.
      destruct i0; try discriminate.
      destruct f ; try discriminate.
    + destruct t ; try discriminate.
      destruct i0; try discriminate.
      destruct f ; try discriminate.
    + destruct t ; try discriminate.
      destruct i1; try discriminate.
      destruct f ; try discriminate.
    + destruct t ; try discriminate.
      destruct i1; try discriminate.
      destruct f ; try discriminate.
  - destruct v; try congruence.
    inv H0.
    unfold classify_cast in CC.
    destruct t1; try discriminate.
    + destruct t; try discriminate.
      destruct i0; discriminate.
      destruct f; discriminate.
    + destruct t; try congruence.
      destruct i1;try congruence.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      constructor.
      destruct f; discriminate.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      econstructor; assumption.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      destruct f; try discriminate.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f0; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
    + destruct t ;
        try congruence.
      destruct i0;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct (Ctypes.intsize_eq
                  Ctypes.I8 Ctypes.I32);
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct (Ctypes.intsize_eq
           Ctypes.I16
           Ctypes.I32)
      ;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct (Ctypes.intsize_eq
           Ctypes.I32
           Ctypes.I32); try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      constructor.
      destruct f. discriminate.
      discriminate.
    +  destruct t ; try congruence.
       destruct i0 ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq
           Ctypes.I8 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I16 Ctypes.I32) ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I32 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ;congruence.
       constructor.
       destruct f; congruence.
    + destruct t ; try congruence.
       destruct i0 ; try congruence.
       destruct Archi.ptr64 ; try congruence.
      destruct (Ctypes.intsize_eq Ctypes.I8 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I16 Ctypes.I32) ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I32 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ;congruence.
       constructor.
       destruct f; congruence.
    + destruct t ; try congruence.
       destruct i1 ; try congruence.
      destruct f; try congruence.
    +        destruct t ; try congruence.
             destruct i1 ; try congruence.
             destruct f ; try congruence.
  - destruct v; try congruence.
    inv H0.
    unfold classify_cast in CC.
    destruct t1; try discriminate.
    + destruct t; try discriminate.
      destruct i0; discriminate.
      destruct f; discriminate.
    + destruct t; try congruence.
      destruct i1;try congruence.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct f ; try discriminate.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      inv CC.
      constructor. apply cast_int_int_idem.
      inv CC.
      constructor. apply cast_int_int_idem.
      inv CC.
      constructor. apply cast_int_int_idem.
      destruct f; discriminate.
      destruct Archi.ptr64 eqn:ARCH; try discriminate.
      inv CC.
      constructor; auto.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f0; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
    + destruct t ;
        try congruence.
      destruct i0;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      inv CC.
      constructor. apply cast_int_int_idem.
      destruct (Ctypes.intsize_eq
                  Ctypes.I8 Ctypes.I32);
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      inv CC.
      constructor. apply cast_int_int_idem.
      destruct (Ctypes.intsize_eq
           Ctypes.I16
           Ctypes.I32)
      ;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      inv CC.
      constructor. apply cast_int_int_idem.
      destruct (Ctypes.intsize_eq
           Ctypes.I32
           Ctypes.I32); try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct f; discriminate.
    +  destruct t ; try congruence.
       destruct i0 ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       inv CC.
       constructor. apply cast_int_int_idem.
       destruct (Ctypes.intsize_eq
           Ctypes.I8 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ; try congruence.
       inv CC.  constructor. apply cast_int_int_idem.
       destruct (Ctypes.intsize_eq Ctypes.I16 Ctypes.I32) ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       inv CC.  constructor. apply cast_int_int_idem.
       destruct (Ctypes.intsize_eq Ctypes.I32 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ;congruence.
       destruct Archi.ptr64 ;congruence.
       destruct f; congruence.
    + destruct t ; try congruence.
       destruct i0 ; try congruence.
       destruct Archi.ptr64 ; try congruence.
      inv CC.  constructor. apply cast_int_int_idem.
      destruct (Ctypes.intsize_eq Ctypes.I8 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ; try congruence.
      inv CC.  constructor. apply cast_int_int_idem.
      destruct (Ctypes.intsize_eq Ctypes.I16 Ctypes.I32) ; try congruence.
       destruct Archi.ptr64 ; try congruence.
      inv CC.  constructor. apply cast_int_int_idem.
      destruct (Ctypes.intsize_eq Ctypes.I32 Ctypes.I32); try congruence.
      destruct Archi.ptr64 ;congruence.
      destruct Archi.ptr64 ;congruence.
       destruct f; congruence.
    + destruct t ; try congruence.
       destruct i1 ; try congruence.
      destruct f; try congruence.
    +        destruct t ; try congruence.
             destruct i1 ; try congruence.
             destruct f ; try congruence.
Qed.

(**r this one should be another version of `Cop.val_casted` *)
Fixpoint vc_casted (inv: list (positive * Ctypes.type)) (e:expr) :=
  match e with
  | Econst_int _ t    => is_Vint t
  | Econst_float _ t  => is_Vfloat t
  | Econst_single _ t => is_Vsingle t
  | Econst_long _ t  => is_Vlong t
  | Evar _ _         => false
  | Etempvar v t     => existsb (fun x => if Ctypes.type_eq t (snd x) then Pos.eqb v (fst x) else false) inv
  | Ederef e _       => false (**r ysh: `false` -> `vc_casted inv e` *)
  | Eaddrof _ _       => false
  | Eunop o e t       => vc_casted inv e && vc_unary_operation_casted o (typeof e) t
  | Ebinop o e1 e2 t    => vc_casted inv e1 && vc_casted inv e2 &&
                             vc_binary_operation_casted o (typeof e1) (typeof e2) t
  | Ecast e ty        => vc_casted inv e &&
                           vc_cast_casted (typeof e) ty
  | Efield e _ _      => false
  | Esizeof _ _       => false
  | Ealignof _ _      => false
  end.

(**r this Lemma tells the relation among vc_casted, exec_expr and `Cop.val_casted` *)
Lemma vc_casted_correct :
  forall inv ge le m a v
         (INV : var_casted_list inv le),
    vc_casted inv a = true ->
    exec_expr ge empty_env le m a = Some v ->
    Cop.val_casted v (typeof a).
Proof.
  induction a; simpl in *; try discriminate.
  - intros. inv H0.
    apply is_Vint_casted; auto.
  - intros. inv H0.
    apply is_Vfloat_casted; auto.
  - intros. inv H0.
    apply is_Vsingle_casted; auto.
  - intros. inv H0.
    apply is_Vlong_casted; auto.
  - intros.
    rewrite existsb_exists in H.
    destruct H as ((i',t'),(IN,P)).
    simpl in P.
    destruct (Ctypes.type_eq t t'); try congruence.
    apply Peqb_true_eq in P. subst.
    eapply INV;eauto.
  - intros.
    destruct (exec_expr ge empty_env le m a) eqn:E1; try discriminate.
    repeat rewrite andb_true_iff in H.
    destruct H as (H1, H3).
    eapply vc_casted_unary_operation_correct in H0; eauto.
  - (**r Ebinop *)
    intros.
    destruct (exec_expr ge empty_env le m a1) eqn:E1; try discriminate.

    destruct (exec_expr ge empty_env le m a2) eqn:E2; try discriminate.
    repeat rewrite andb_true_iff in H.
    destruct H as ((H1 , H2), H3).
    eapply vc_casted_binary_operation_correct in H0; eauto.
  - intros.
    destruct (exec_expr ge empty_env le m a) eqn:E1; try discriminate.
    repeat rewrite andb_true_iff in H.
    destruct H as (H1 , H2).
    specialize (IHa _ INV H1 eq_refl).
    eapply val_casted_sem_cast in H0; eauto.
Qed.

Lemma check_cast : forall ge le inv m eargs lval targs
                          (INV   : var_casted_list inv le)
                          (LVAL : map_opt (exec_expr ge empty_env le m) eargs = Some lval)
                          (TARGS : List.map typeof eargs = List.map snd targs)
                          (CAST  : List.forallb (vc_casted inv) eargs = true)
  ,
    Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => Cop.val_casted v (snd t)) lval targs.
Proof.
  induction eargs.
  - simpl. intros. inv TARGS.
    inv LVAL. destruct targs. constructor.
    discriminate.
  - intros.
    simpl in TARGS. simpl in LVAL.
    destruct (exec_expr ge empty_env le m a) eqn:E ; try discriminate.
    destruct (map_opt (exec_expr ge empty_env le m) eargs) eqn:M ; try discriminate.
    inv LVAL. destruct targs. discriminate.
    inv TARGS.
    simpl in CAST.
    rewrite andb_true_iff in CAST.
    destruct CAST as (C1 & C2).
    econstructor ; eauto.
    rewrite <- H0.
    eapply vc_casted_correct;eauto.
Qed.

Lemma var_casted_list_map_fst : forall {St: Type} (st:St) m le var_inv,
    Forall (match_elt st m le) var_inv ->
  var_casted_list (map fst var_inv) le.
Proof.
 unfold var_casted_list.
 intros.
 rewrite Forall_forall in H.
 rewrite in_map_iff in H0.
 destruct H0 as (((i1,t1),r1), (EQ , IN)).
 simpl in EQ. inv EQ.
 apply H in IN.
 unfold match_elt in IN.
 simpl in IN.
 rewrite H1 in IN.
 tauto.
Qed.

Fixpoint type_of_list (l : list Ctypes.type) : Ctypes.typelist :=
  match l with
  | nil => Ctypes.Tnil
  | cons e l => Ctypes.Tcons e (type_of_list l)
  end.


Lemma in_inv_of_modifies : forall {St: Type} x md (l : list
         (positive * Ctypes.type * Inv St)),
  In x (inv_of_modifies md l) -> In x l.
Proof.
  unfold inv_of_modifies.
  destruct md; auto.
  intros. unfold filter_inv in H.
  rewrite filter_In in H. tauto.
Qed.

Lemma match_temp_env_inv_of_modifies :
  forall {St: Type} md m m' (st st': St) var_inv le
    (UNMOD : unmodifies_effect md m m' st st')
    (ALL   : Forall (match_elt st m le) var_inv),
    match_temp_env (inv_of_modifies md var_inv) le st' m'.
Proof.
  unfold match_temp_env.
  destruct md; simpl; auto.
  - intuition subst. auto.
  - intros.
    rewrite Forall_forall in ALL.
    rewrite Forall_forall.
    intros. unfold filter_inv in H.
    rewrite filter_In in H.
    destruct H as (IN & ST).
    destruct x. destruct p.
    apply ALL in IN. clear ALL.
    unfold match_elt in *.
    simpl in *.
    destruct (Maps.PTree.get i0 le); try tauto.
    destruct i ; try discriminate.
    simpl in *. tauto.
Qed.

Section S.
  Variable St : Type.
  Variable p : program.
  Variable fn: Clight.function.



  Lemma correct_statement_call :
    forall  (has_cast : bool) args res (f : arrow_type args (M St res)) is_pure a loc
           vres fvar targs ti eargs tres  fct modifies
           (FS : Globalenvs.Genv.find_symbol (globalenv (semantics2 p)) fvar = Some loc)
           (FF : Globalenvs.Genv.find_funct (globalenv (semantics2 p))
                                            (Vptr loc Ptrofs.zero) = Some (Ctypes.Internal fct))
           (TF : type_of_fundef (Ctypes.Internal fct) =
                   Ctypes.Tfunction targs ti AST.cc_default)

           (match_state : St -> mem -> Prop)
           (match_arg : DList.t (fun x : Type => x -> Inv St) (all_args args is_pure))
           (match_res : res -> Inv St)
           (C : correct_function St p args res f fct modifies  is_pure match_state match_arg match_res a)
           (var_inv : list (positive * Ctypes.type * Inv St))
           (le : temp_env) (m : Memory.Mem.mem) (st : St)
(*           (VARINV: var_inv_preserve var_inv match_res modifies  le)*)
           (TI    : ti = fn_return fct)
           (TARGS : targs = type_of_list (map typeof eargs))
           (TARGS1 : map typeof eargs = map snd (fn_params fct))
           (NOTIN1 : ~In vres   (map  (fun x  => fst (fst x)) var_inv))
           (NOTIN2 : ~In tres   (map  (fun x  => fst (fst x)) var_inv))
           (CASTED  : List.forallb (vc_casted (List.map fst var_inv)) eargs = true)
           (LENEARGS : List.length eargs = (List.length (all_args args is_pure)))
           (LVAL  :
             Forall (match_elt st m le) var_inv ->
             exists lval,
               map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs = Some lval
            /\ forall (LEN :List.length lval = (List.length (all_args args is_pure))),
      DList.Forall2 (fun (a : Type) (R : a -> Inv St) (X : a * val) => eval_inv (R (fst X)) (snd X) st m) match_arg
                    (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN)))
    ,
      correct_statement St p res (cl_app f a) fn
    (Ssequence
       (Scall (Some tres)
          (Evar fvar
             (Ctypes.Tfunction targs ti AST.cc_default))
          eargs)
       (Sset vres (if has_cast then
          (Ecast (Etempvar tres ti) ti) else Etempvar tres ti)))
    modifies (pre  match_state var_inv) (post  modifies match_state match_res var_inv (vres,ti)) st le m.
  Proof.
    repeat intro.
    rename H into PRE.
    destruct C.
    specialize (fn_eval_ok4  st).
    destruct (cl_app f a st); try congruence.
    destruct p0 as (v',st').
    intros s' k k' K.
    unfold pre in PRE. unfold match_temp_env in PRE.
    destruct PRE as (MS & PRE).
    destruct (LVAL PRE) as (lval & MAP & ALL).
    clear LVAL.
    assert (LEN : Datatypes.length lval = Datatypes.length (all_args args is_pure)).
    {
      apply length_map_opt in MAP.
      rewrite <- MAP.
      rewrite LENEARGS.
      reflexivity.
      }
      specialize (ALL LEN).
      specialize (fn_eval_ok4 (DList.of_list_sl lval (all_args args is_pure) LEN)
                            (Kcall (Some tres) fn empty_env le
                                   (Kseq (Sset vres (if has_cast
                then Ecast (Etempvar tres ti) ti
                                                     else Etempvar tres ti)) k)) m).

    assert (EQ: lval = (DList.to_list (fun (_ : Type) (v : val) => v)
                                   (DList.of_list_sl lval (all_args args is_pure) LEN))).
    { apply (DList.to_list_of_list_sl ). }

    assert (ALLCASTED : Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => val_casted v (snd t))
    lval (fn_params fct)).
    {
      eapply check_cast; eauto.
      eapply var_casted_list_map_fst; eauto.
    }
    destruct (fn_eval_ok4 MS ALL) as (v1 & m1 & t1 & STAR & RES' & CAST  &MOD & MS').
    rewrite <- EQ. assumption.
    do 3 eexists.
    split.
    eapply star_step.
    econstructor ;eauto.
    eapply star_step.
    econstructor ;eauto.
    simpl. reflexivity.
    econstructor ;eauto.
    eapply eval_Evar_global.
    apply Maps.PTree.gempty.
    eauto.
    eapply deref_loc_reference.
    simpl; reflexivity.
    { instantiate (1:= lval).
      revert PRE CASTED TARGS MAP.
      clear. intro. revert lval targs.
      induction eargs.
      - simpl. intros. inv MAP.
        constructor.
      - simpl.
        intros. subst.
        destruct (exec_expr (Clight.globalenv p) empty_env le m a) eqn:E; try congruence.
        destruct (map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs) eqn:MO; try discriminate.
        inv MAP.
        rewrite andb_true_iff in CASTED.
        destruct CASTED as (C1 & C2).
        econstructor; eauto.
        apply eval_expr_eval in E.
        eauto.
        apply Cop.cast_val_casted.
        eapply vc_casted_correct; eauto.
        eapply var_casted_list_map_fst; eauto.
    }
    eapply star_trans.
    rewrite <- EQ in STAR.
    eauto.
    unfold call_cont.
    eapply star_step.
    econstructor ; eauto.
    eapply star_step.
    econstructor ; eauto.
    eapply star_step; eauto.
    econstructor ; eauto.
    {
      instantiate (1:=v1).
      destruct has_cast.
      econstructor;eauto.
      econstructor;eauto.
      unfold set_opttemp.
      rewrite Maps.PTree.gss. reflexivity.
      simpl.
      apply Cop.cast_val_casted; auto.
      subst. auto.
      econstructor; eauto.
      unfold set_opttemp.
      rewrite Maps.PTree.gss. reflexivity.
    }
    eapply star_step.
    eapply apply_cont_cont; eauto.
    apply star_refl.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    unfold post.
    split_and; auto.
    unfold match_temp_env.
    apply Forall_cons.
    - unfold match_elt.
      simpl.
      rewrite Maps.PTree.gss.
      subst. tauto.
    - apply match_temp_env_set; auto.
      intro.
      rewrite in_map_iff in H.
      destruct H as (x & EQIN & IN).
      apply in_inv_of_modifies in IN.
      apply NOTIN1.
      rewrite in_map_iff. exists x. tauto.
      apply match_temp_env_set; auto.
      intro.
      rewrite in_map_iff in H.
      destruct H as (x & EQIN & IN).
      apply in_inv_of_modifies in IN.
      apply NOTIN2.
      rewrite in_map_iff. exists x. tauto.
      revert PRE.
      apply match_temp_env_inv_of_modifies; auto.
  Qed.

End S.

Section S.
  Variable St : Type.
  Variable p : program.
  Variable fn: Clight.function.

  Lemma correct_statement_call_none :
    forall args  (f : arrow_type args (M St unit)) is_pure a loc
           fvar targs ti eargs fct modifies
           (FS : Globalenvs.Genv.find_symbol (globalenv (semantics2 p)) fvar = Some loc)
           (FF : Globalenvs.Genv.find_funct (globalenv (semantics2 p))
                                            (Vptr loc Ptrofs.zero) = Some (Ctypes.Internal fct))
           (TF : type_of_fundef (Ctypes.Internal fct) =
                   Ctypes.Tfunction targs ti AST.cc_default)
           (match_state : St -> mem -> Prop)
           (match_arg : DList.t (fun x : Type => x -> Inv St) (all_args args is_pure))
           (match_res : unit -> Inv St)
           (C : correct_function St p args unit f fct modifies is_pure match_state match_arg match_res a)
           (match_res_Vundef : forall x v st m, eval_inv (match_res x) v st m -> v = Vundef)

           (var_inv : list (positive * Ctypes.type * Inv St))
           (le : temp_env) (m : Memory.Mem.mem) (st : St)
(*           (VARINV: var_inv_preserve var_inv match_res modifies  le)*)
           (TI    : ti = fn_return fct)
           (TARGS : targs = type_of_list (map typeof eargs))
           (TARGS1 : map typeof eargs = map snd (fn_params fct))
           (CASTED  : List.forallb (vc_casted (List.map fst var_inv)) eargs = true)
           (LENEARGS : List.length eargs = (List.length (all_args args is_pure)))
           (LVAL  :
             Forall (match_elt st m le) var_inv ->
             exists lval,
               map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs = Some lval
            /\ forall (LEN :List.length lval = (List.length (all_args args is_pure))),
      DList.Forall2 (fun (a : Type) (R : a -> Inv St) (X : a * val) => eval_inv (R (fst X)) (snd X) st m) match_arg
                    (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN)))
    ,
      correct_statement St p unit (cl_app f a) fn
       (Scall None
          (Evar fvar
             (Ctypes.Tfunction targs ti AST.cc_default))
          eargs)
    modifies (pre  match_state var_inv) (post_unit modifies match_state match_res  (inv_of_modifies modifies var_inv)) st le m.
  Proof.
    repeat intro.
    rename H into PRE.
    destruct C.
    specialize (fn_eval_ok4  st).
    destruct (cl_app f a st); try congruence.
    destruct p0 as (v',st').
    intros s' k k' K.
    unfold pre in PRE. unfold match_temp_env in PRE.
    destruct PRE as (MS& PRE).
    destruct (LVAL PRE) as (lval & MAP & ALL).
    clear LVAL.
    assert (LEN : Datatypes.length lval = Datatypes.length (all_args args is_pure)).
    {
      apply length_map_opt in MAP.
      rewrite <- MAP.
      rewrite LENEARGS.
      reflexivity.
      }
      specialize (ALL LEN).
      specialize (fn_eval_ok4 (DList.of_list_sl lval (all_args args is_pure) LEN)
                            (Kcall None fn empty_env le
                                    k) m).
    assert (EQ: lval = (DList.to_list (fun (_ : Type) (v : val) => v)
                                   (DList.of_list_sl lval (all_args args is_pure) LEN))).
    { apply (DList.to_list_of_list_sl ). }
    assert (ALLCASTED : Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => val_casted v (snd t))
    lval (fn_params fct)).
    {
      eapply check_cast; eauto.
      eapply var_casted_list_map_fst; eauto.
    }
    destruct (fn_eval_ok4 MS ALL) as (v1 & m1 & t1 & STAR & RES' & CAST  &MOD & MS').
    rewrite <- EQ. assumption.
    assert (v1 = Vundef). eapply match_res_Vundef; eauto.
    subst.
    do 3 eexists.
    split.
    eapply star_step.
    econstructor ;eauto.
    simpl. reflexivity.
    econstructor ;eauto.
    eapply eval_Evar_global.
    apply Maps.PTree.gempty.
    eauto.
    eapply deref_loc_reference.
    simpl; reflexivity.
    { instantiate (1:= lval).
      revert PRE CASTED  MAP.
      clear. intro. revert lval.
      induction eargs.
      - simpl. intros. inv MAP.
        constructor.
      - simpl.
        intros. subst.
        destruct (exec_expr (Clight.globalenv p) empty_env le m a) eqn:E; try congruence.
        destruct (map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs) eqn:MO; try discriminate.
        inv MAP.
        rewrite andb_true_iff in CASTED.
        destruct CASTED as (C1 & C2).
        econstructor; eauto.
        apply eval_expr_eval in E.
        eauto.
        apply Cop.cast_val_casted.
        eapply vc_casted_correct; eauto.
        eapply var_casted_list_map_fst; eauto.
    }
    eapply star_trans.
    rewrite <- EQ in STAR.
    eauto.
    unfold call_cont.
    eapply star_step.
    econstructor ; eauto.
    unfold set_opttemp.
    eapply star_step.
    eapply apply_cont_cont; eauto.
    apply star_refl.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    unfold post_unit.
    repeat split; auto.
    eapply match_temp_env_inv_of_modifies; eauto.
  Qed.

End S.



Section S.
  Variable St : Type.
  Variable p : program.
  Variable fn: Clight.function.

  Lemma correct_body_call_ret :
    forall  (has_cast : bool) args res (f : arrow_type args (M St res)) is_pure a loc
           (*vres*) fvar targs ti eargs tres  fct modifies
           (FS : Globalenvs.Genv.find_symbol (globalenv (semantics2 p)) fvar = Some loc)
           (FF : Globalenvs.Genv.find_funct (globalenv (semantics2 p))
                                            (Vptr loc Ptrofs.zero) = Some (Ctypes.Internal fct))
           (TF : type_of_fundef (Ctypes.Internal fct) =
                   Ctypes.Tfunction targs ti AST.cc_default)
           (match_state : St -> mem -> Prop)
           (match_arg : DList.t (fun x : Type => x -> Inv St) (all_args args is_pure))
           (match_res : res -> Inv St)
           (C : correct_function St p args res f fct modifies is_pure match_state match_arg match_res a)
           (var_inv : list (positive * Ctypes.type * Inv St))
           (le : temp_env) (m : Memory.Mem.mem) (st : St)
           (TI    : ti = fn_return fct)
           (TIN    : ti = fn_return fn)
           (TARGS : targs = type_of_list (map typeof eargs))
           (TARGS1 : map typeof eargs = map snd (fn_params fct))
(*           (NOTIN1 : ~In vres   (map  (fun x  => fst (fst x)) var_inv))
           (NOTIN2 : ~In tres   (map  (fun x  => fst (fst x)) var_inv)) *)
           (CASTED  : List.forallb (vc_casted (List.map fst var_inv)) eargs = true)
           (LENEARGS : List.length eargs = (List.length (all_args args is_pure)))
           (LVAL  :
             Forall (match_elt st m le) var_inv ->
             exists lval,
               map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs = Some lval
            /\ forall (LEN :List.length lval = (List.length (all_args args is_pure))),
      DList.Forall2 (fun (a : Type) (R : a -> Inv St) (X : a * val) => eval_inv (R (fst X)) (snd X) st m) match_arg
                    (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN)))
    ,
      correct_body St p res (cl_app f a) fn
    (Ssequence
       (Scall (Some tres)
          (Evar fvar
             (Ctypes.Tfunction targs ti AST.cc_default))
          eargs)
       (Sreturn (Some (if has_cast then
                   (Ecast (Etempvar tres ti) ti) else Etempvar tres ti))))
    modifies match_state var_inv match_res  st le m.
  Proof.
    repeat intro.
    rename H into PRE.
    destruct C.
    specialize (fn_eval_ok4  st).
    destruct (cl_app f a st); try congruence.
    destruct p0 as (v',st').
    intros k.
    destruct (LVAL PRE) as (lval & MAP & ALL).
    clear LVAL.
    assert (LEN : Datatypes.length lval = Datatypes.length (all_args args is_pure)).
    {
      apply length_map_opt in MAP.
      rewrite <- MAP.
      rewrite LENEARGS.
      reflexivity.
      }
      specialize (ALL LEN).
      specialize (fn_eval_ok4 (DList.of_list_sl lval (all_args args is_pure) LEN)
                            (Kcall (Some tres) fn empty_env le
                                   (Kseq (Sreturn
                (Some
                   (if has_cast
                    then Ecast (Etempvar tres ti) ti
                    else Etempvar tres ti))) k)) m).
    assert (EQ: lval = (DList.to_list (fun (_ : Type) (v : val) => v)
                                   (DList.of_list_sl lval (all_args args is_pure) LEN))).
    { apply (DList.to_list_of_list_sl ). }

    (*rewrite EQ in MA''.*)
    assert (ALLCASTED : Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => val_casted v (snd t))
    lval (fn_params fct)).
    {
      eapply check_cast; eauto.
      eapply var_casted_list_map_fst; eauto.
    }
    destruct (fn_eval_ok4 MS ALL) as (v1 & m1 & t1 & STAR & RES' & CAST  &MOD & MS').
    rewrite <- EQ. assumption.
    do 3 eexists.
    split.
    eapply star_step.
    econstructor ;eauto.
    eapply star_step.
    econstructor ;eauto.
    simpl. reflexivity.
    econstructor ;eauto.
    eapply eval_Evar_global.
    apply Maps.PTree.gempty.
    eauto.
    eapply deref_loc_reference.
    simpl; reflexivity.
    { instantiate (1:= lval).
      revert PRE CASTED TARGS MAP.
      clear. intro. revert lval targs.
      induction eargs.
      - simpl. intros. inv MAP.
        constructor.
      - simpl.
        intros. subst.
        destruct (exec_expr (Clight.globalenv p) empty_env le m a) eqn:E; try congruence.
        destruct (map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs) eqn:MO; try discriminate.
        inv MAP.
        rewrite andb_true_iff in CASTED.
        destruct CASTED as (C1 & C2).
        econstructor; eauto.
        apply eval_expr_eval in E.
        eauto.
        apply Cop.cast_val_casted.
        eapply vc_casted_correct; eauto.
        eapply var_casted_list_map_fst; eauto.
    }
    eapply star_trans.
    rewrite <- EQ in STAR.
    eauto.
    unfold call_cont.
    eapply star_step.
    econstructor ; eauto.
    econstructor ; eauto.
    econstructor; eauto.
    econstructor ; eauto.
    econstructor ; eauto.
    {
      instantiate (1:=v1).
      destruct has_cast.
      econstructor;eauto.
      econstructor;eauto.
      unfold set_opttemp.
      rewrite Maps.PTree.gss. reflexivity.
      simpl.
      apply Cop.cast_val_casted; auto.
      subst. auto.
      econstructor; eauto.
      unfold set_opttemp.
      rewrite Maps.PTree.gss. reflexivity.
    }
    rewrite TI in *.
    rewrite TIN in *.
    unfold typeof.
    destruct has_cast.
    eapply cast_val_casted; eauto.
    eapply cast_val_casted; eauto.
    reflexivity.
    econstructor;eauto.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    repeat split; auto.
    congruence.
  Qed.
End S.

Section S.
  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable args : list Type.
  Variable res : Type.

  Variable f : arrow_type args (M St res).
  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Lemma correct_function_modifies_more : forall mods mods' is_pure match_state match_args matchres a
(CF : correct_function St p args res f fn mods' is_pure match_state match_args matchres a)
(INCL :incl_modifies mods' mods) ,
   correct_function St p args res f fn mods is_pure match_state match_args matchres a.
Proof.
  repeat intro.
  destruct CF.
  econstructor.
  intros.
  specialize (fn_eval_ok4 st).
  destruct (cl_app f a st);auto.
  destruct p0 ; auto.
  intros.
  destruct (fn_eval_ok4 lval k m MS H H0) as (v & m' & t & ST & MR & CS & UN & MS').
  repeat eexists; repeat split;eauto.
  eapply unmodifies_effect_mono; eauto.
Qed.

End S.

Section S.
  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res1 : Type.

  Variable f1 : M St res1.

  Variable res2 : Type.

  Variable f2 : res1 -> (M St res2).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_res1 : res1 -> Inv St.

  Variable match_res2 : res2  -> Inv St.

  Variable match_state : St -> mem -> Prop.

  Lemma correct_statement_seq_body :
    forall (s1 s2:Clight.statement) vret ti
           (modifies1 modifies2 modifiesr: modifies_spec)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m
      (C1  : correct_statement St p res1 f1 fn s1 modifies1 (pre match_state var_inv) (post modifies1 match_state match_res1 var_inv (vret,ti)) st le m)
      (C2  : forall le m st x, correct_body St p res2 (f2 x) fn s2 modifies2 match_state ((vret,ti,match_res1 x):: (inv_of_modifies modifies1 var_inv)) match_res2 st le m)
      (MOD : lub_modifies modifies1 modifies2 = modifiesr)
    ,
             correct_body St p  res2 (bindM f1 f2) fn
             (Ssequence s1 s2) modifiesr  match_state var_inv match_res2 st le m.
  Proof.
    intros.
    subst.
    unfold correct_body.
    intros MS PRE.
    unfold bindM.
    unfold correct_statement in C1.
    destruct (f1 st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    destruct (f2 v1 st1) eqn:F2; try congruence.
    destruct p0 as (v2,st2).
    intros.
    destruct (C1 (conj MS PRE) s2 (Kseq s2 k) k  eq_refl) as
      (le'& m' & t & ST & MR & MOD).
    specialize (C2 le' m' st1 v1).
    unfold correct_body in C2.
    rewrite F2 in C2.
    assert (PRE2 : pre match_state ((vret, ti, match_res1 v1) :: inv_of_modifies modifies1 var_inv) st1 le' m').
    {
      unfold pre. unfold post in MR.
      tauto.
    }
    destruct (C2 (proj1 PRE2) (proj2 PRE2)  k) as
      (le2& m2 & t2 & ST2 & MR2).
    exists le2. exists m2. exists (t ++ t2).
    split;auto.
    eapply star_step.
    econstructor ; eauto.
    eapply star_trans.
    eauto.
    eauto.
    reflexivity.
    reflexivity.
    repeat split ; try tauto.
    generalize (incl_lub_left modifies1 modifies2) as I1.
    generalize (incl_lub_right modifies1 modifies2) as I2.
    intros.
    destruct MR2 as (_ &  _ & MOD2).
    eapply unmodifies_effect_trans.
    eapply unmodifies_effect_mono. apply I1.
    apply MOD.
    eapply unmodifies_effect_mono. apply I2.
    auto.
    tauto.
    auto.
    auto.
Qed.

End S.

Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable f1 : M St unit.

  Variable res2 : Type.

  Variable f2 : unit -> (M St res2).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable modifies : modifies_spec.

  Variable match_state : St -> mem -> Prop.

  Variable match_res1 : unit -> Inv St.

  Variable match_res2 : res2  -> Inv St.

  Lemma correct_statement_seq_body_unit :
    forall (s1 s2:Clight.statement)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m
      (C1 : correct_statement St p unit f1 fn s1 modifies (pre match_state var_inv) (post_unit modifies match_state match_res1 var_inv) st le m)
      (C2 : forall le m st x, correct_body St p res2 (f2 x) fn s2 modifies match_state var_inv match_res2 st le m)
    ,
             correct_body St p  res2 (bindM f1 f2) fn
             (Ssequence s1 s2) modifies match_state var_inv match_res2 st le m.
  Proof.
    intros.
    unfold correct_body.
    intros MS PRE.
    unfold bindM.
    unfold correct_statement in C1.
    destruct (f1 st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    destruct (f2 v1 st1) eqn:F2; try congruence.
    destruct p0 as (v2,st2).
    intros.
    destruct (C1 (conj MS PRE) s2 (Kseq s2 k) k  eq_refl) as
      (le'& m' & t & ST & MR & MOD).
    specialize (C2 le' m' st1 v1).
    unfold correct_body in C2.
    rewrite F2 in C2.
    assert (PRE2 : pre match_state var_inv st1 le' m').
    {
      unfold pre. unfold post_unit in MR.
      tauto.
    }
    destruct (C2 (proj1 PRE2) (proj2 PRE2)  k) as
      (le2& m2 & t2 & ST2 & MR2).
    exists le2. exists m2. exists (t ++ t2).
    split;auto.
    eapply star_step.
    econstructor ; eauto.
    eapply star_trans.
    eauto.
    eauto.
    reflexivity.
    reflexivity.
    repeat split ; try tauto.
    eapply unmodifies_effect_trans; eauto.
    tauto.
    auto.
    auto.
  Qed.

End S.

Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f : M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_state : St -> mem -> Prop.

  Variable match_res : res -> Inv St.


  Lemma correct_statement_seq_body_drop :
    forall (s1 s2:Clight.statement)
           (modifies : modifies_spec)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m
      (C2 : forall le m st, correct_body St p res f fn s1 modifies match_state var_inv match_res st le m)
    ,
             correct_body St p  res f fn
             (Ssequence s1 s2) modifies  match_state var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros MS PRE.
    unfold correct_body in C2.
    specialize (C2 le m st MS PRE).
    destruct (f st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    intros.
    destruct (C2 (Kseq s2 k)) as (vr & mr & tr & STAR & MR & VC & UNM & MS').
    exists vr, mr,tr.
    repeat split; auto.
    eapply star_step.
    econstructor;eauto.
    eauto. reflexivity.
  Qed.
End S.



Lemma bind_id_left : forall {A St: Type} (f: M St A) x  , f x = bindM (returnM tt) (fun _ => f) x.
Proof.
  intros.
  unfold bindM.
  unfold returnM.
  reflexivity.
Qed.

Lemma correct_body_id : forall {St: Type} p (res:Type) (f: M St res) fn (s:statement) md ms pr pst st le m,
    correct_body St p res (bindM (returnM tt) (fun _ => f)) fn s md ms pr pst st le m ->
    correct_body St p res f fn s md ms pr pst st le m.
Proof.
  repeat intro.
  unfold correct_body in H.
  rewrite <- bind_id_left in H.
  apply H; auto.
Qed.

Lemma bind_id_right : forall {A St: Type} (f: M St A) x  , f x = bindM f returnM x.
Proof.
  intros.
  unfold bindM.
  unfold returnM.
  destruct (f x); auto. destruct p; auto.
Qed.

Lemma correct_body_id_right : forall {St: Type} p (res:Type) (f: M St res) fn (s:statement) md ms pr pst st le m,
    correct_body St p res (bindM f returnM) fn s md ms pr pst st le m ->
    correct_body St p res f fn s md ms pr pst st le m.
Proof.
  repeat intro.
  unfold correct_body in H.
  rewrite <- bind_id_right in H.
  apply H; auto.
Qed.



Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f : M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_state : St -> mem -> Prop.

  Variable match_res1 : Inv St.

  Variable match_res2 : res  -> Inv St.

  Lemma correct_statement_seq_set :
    forall (r:AST.ident) (e:expr) (s2:Clight.statement) (*vret ti*)
           (modifies : modifies_spec)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m 
      (EVAL: match_state st m -> match_temp_env var_inv le st m ->
             exists v, exec_expr (globalenv (semantics2 p)) empty_env le m e = Some v  /\
                         (eval_inv match_res1  v st m /\val_casted v (typeof e)))
      (FR     :   ~ In r (map (fun x => fst (fst x)) var_inv))
     (C2 : forall le st  m, correct_body St p res f fn s2 modifies  match_state ((r,typeof e,match_res1):: var_inv) match_res2 st le m)
    ,
             correct_body St p  res f fn
             (Ssequence (Sset r e) s2) modifies match_state  var_inv match_res2 st le m.
  Proof.
    intros.
    apply correct_body_id.
    eapply correct_statement_seq_body with (modifies1:=ModNothing).
    instantiate (1 := typeof e).
    instantiate (1 := r).
    instantiate (1:= fun _ => match_res1).
    - repeat intro.
    unfold pre in H. destruct H as (MS & MT).
    specialize (EVAL MS MT).
    destruct EVAL as (v & EVAL & MR & CAST).
    apply eval_expr_eval in EVAL.
    repeat eexists.
    econstructor. econstructor.
    eauto.
    econstructor.
    eapply apply_cont_cont. eauto.
    econstructor ; eauto.
    reflexivity.
    reflexivity.
    assumption.
    apply match_temp_env_cons.
    unfold match_elt.
    simpl.
    rewrite Maps.PTree.gss.
    split ; auto.
    eapply match_temp_env_set; auto.
    - intros.
      eauto.
    - reflexivity.
  Qed.

End S.




Definition set_bool (vr: positive) (b:bool) (le: temp_env) :=
  Maps.PTree.set vr (if b then Vint Int.one else Vint Int.zero) le.

Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f1 f2 : M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

 Variable match_state : St -> mem -> Prop.

  Variable match_res : res -> Inv St.


  Lemma correct_statement_if_body :
    forall (s1 s2:Clight.statement) (x:bool) vr
           (modifies : modifies_spec)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m
      (IN : In (vr, Clightdefs.tbool, (StateLess St (match_bool x))) var_inv)
      (C1 : correct_body St p res (if x then f1 else f2) fn (if x then s1 else s2)
                         modifies match_state  var_inv match_res st
                         le m)
    ,

      correct_body St p res (if x then f1 else f2) fn
                          (Sifthenelse (Etempvar vr Clightdefs.tbool)
                                       s1 s2) modifies match_state var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros MS PRE.
    unfold correct_body in C1.
    specialize(C1 MS PRE).
    assert (GET : Maps.PTree.get vr le = Some (Vint (if x then Int.one else Int.zero))).
    {
      unfold match_temp_env in PRE.
      rewrite Forall_forall in PRE.
      apply PRE in IN.
      unfold match_elt in IN.
      simpl in IN.
      destruct (Maps.PTree.get vr le).
      destruct IN.
      unfold stateless,match_bool in H.
      subst. reflexivity.
      tauto.
    }
    destruct x;auto.
    - destruct (f1 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      econstructor ;eauto.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto. auto.
    - destruct (f2 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      econstructor ;eauto.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto. auto.
  Qed.

End S.

Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f1 f2 : M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_state : St -> mem -> Prop.

  Variable match_res : res -> Inv St.

  Lemma correct_statement_if_body_expr :
    forall (s1 s2:Clight.statement) (x:bool) e
           (modifies : modifies_spec)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m
(C1 :
forall
       (EXEC : exec_expr (globalenv (semantics2 p)) empty_env le m e = Some (Val.of_bool x)),
correct_body St p res (if x then f1 else f2) fn (if x then s1 else s2)
                         modifies match_state var_inv match_res st
                         le m)
      (TY : classify_bool (typeof e) = bool_case_i)
      (EVAL: match_state st m -> match_temp_env var_inv le st m -> exec_expr (globalenv (semantics2 p)) empty_env le m e = Some (Val.of_bool x))
    ,

      correct_body St p res (if x then f1 else f2) fn
                          (Sifthenelse e
                                       s1 s2) modifies match_state var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros MS PRE.
    unfold correct_body in C1.
    specialize (EVAL MS PRE).
    specialize(C1 EVAL MS PRE).
    destruct x;auto.
    - destruct (f1 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
      apply eval_expr_eval in EVAL.
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      unfold bool_val.
      simpl.
      rewrite TY.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto. auto.
    - destruct (f2 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
      apply eval_expr_eval in EVAL.
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      unfold bool_val.
      rewrite TY.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto. auto.
  Qed.

End S.

Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f : M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_state : St -> mem -> Prop.

  Variable match_res : res -> Inv St.


  Lemma correct_statement_switch_ex :
    forall e l
           (modifies : modifies_spec)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m

      (TY : classify_switch (typeof e) = switch_case_i)
      (EVAL: match_state st m -> match_temp_env var_inv le st m ->
             exists n,
               exec_expr (globalenv (semantics2 p)) empty_env le m e = Some (Vint (Int.repr n)) /\  0 <= n < Int.modulus /\
                 correct_body St p res f fn (seq_of_labeled_statement (select_switch n l))                            modifies match_state var_inv match_res st
                              le m)
    ,

      correct_body St p res f fn
                          (Sswitch e l) modifies match_state var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros MS PRE.
    specialize (EVAL MS PRE).
    destruct EVAL as (n & EVAL & SMALL & CB).
    unfold correct_body in CB.
    destruct (f st) eqn:F1; try auto.
    destruct p0 as (v',st').
    intros.
    destruct (CB MS PRE (Kswitch k)) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
    apply eval_expr_eval in EVAL.
    exists v1,m1,t1.
    repeat split.
    eapply star_step.
    econstructor ;eauto.
    unfold sem_switch_arg.
    rewrite TY. reflexivity.
    rewrite Int.unsigned_repr_eq.
    rewrite Zmod_small by auto.
    eauto.
    reflexivity.
    auto.
    auto.
    auto. auto.
  Qed.

End S.


Section S.

  Variable St : Type.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f : M St res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_state : St -> mem -> Prop.

  Variable match_res : res -> Inv St.


  Lemma correct_statement_switch :
    forall (n:Z) e l
           (modifies : modifies_spec)
           (var_inv  : list (positive * Ctypes.type * Inv St))
      st le m

      (C1 : correct_body St p res f fn (seq_of_labeled_statement (select_switch n l))
                         modifies match_state var_inv match_res st
                         le m)
      (TY : classify_switch (typeof e) = switch_case_i)
      (EVAL: match_state st m -> match_temp_env var_inv le st m ->
               exec_expr (globalenv (semantics2 p)) empty_env le m e = Some (Vint (Int.repr n)))
      (SMALL : 0 <= n < Int.modulus)
    ,

      correct_body St p res f fn
                          (Sswitch e l) modifies match_state var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros MS PRE.
    unfold correct_body in C1.
    specialize(C1 MS PRE).
    specialize (EVAL MS PRE).
    destruct (f st) eqn:F1; try auto.
    destruct p0 as (v',st').
    intros.
    destruct (C1 (Kswitch k)) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
    apply eval_expr_eval in EVAL.
    exists v1,m1,t1.
    repeat split.
    eapply star_step.
    econstructor ;eauto.
    unfold sem_switch_arg.
    rewrite TY. reflexivity.
    rewrite Int.unsigned_repr_eq.
    rewrite Zmod_small by auto.
    eauto.
    reflexivity.
    auto.
    auto.
    auto. auto.
  Qed.

End S.

Lemma correct_body_Sreturn_None :
  forall {St:Type} p fn modifies inv
         (match_state : St -> mem -> Prop)
         (match_res : unit -> Inv St)
         st le m,
    (match_state st m -> match_temp_env inv le st m -> eval_inv (match_res tt) Vundef st m) ->
    (fn_return fn = Ctypes.Tvoid) ->

    correct_body St p unit (returnM tt) fn (Sreturn None) modifies
               match_state inv match_res st le m.
Proof.
  repeat intro.
  eexists Vundef.
  exists m. exists Events.E0.
  repeat split; auto.
  - eapply star_step.
  econstructor ; eauto.
  reflexivity.
  eapply star_refl.
  reflexivity.
  - rewrite H0.
  constructor.
  - apply unmodifies_effect_refl.
Qed.

Lemma correct_body_Sreturn_Some :
  forall {St:Type} p fn modifies inv A
        (match_state : St -> mem -> Prop)
        (match_res : A -> Inv St)
         st le m a  e
    (EVALRES: match_state st m -> match_temp_env inv le st m ->
   exists v,
     exec_expr (Clight.globalenv p) empty_env le m e = Some v /\
     eval_inv (match_res a) v st m  /\
       sem_cast v (typeof e) (fn_return fn) m = Some v /\ (val_casted v (fn_return fn) -> val_casted v (typeof e))
),

    correct_body St p A (returnM a) fn (Sreturn (Some e)) modifies
               match_state inv match_res st le m.
Proof.
  repeat intro.
  destruct (EVALRES MS H) as (v & EVAL & MR & CASTED & RET).
  eexists v.
  exists m. exists Events.E0.
  assert (VC : val_casted v (typeof e)).
  {
    apply cast_val_is_casted in CASTED.
    auto.
  }
  repeat split; auto.
  - eapply star_step.
    econstructor ; eauto.
    apply eval_expr_eval; auto.
    reflexivity.
    eapply star_refl.
    reflexivity.
  -    eapply cast_val_is_casted. eauto.
  - apply unmodifies_effect_refl.
Qed.



Lemma match_temp_env_ex : forall {St:Type} l' l le (st:St) m ,
    incl l' (List.map fst l) ->
    match_temp_env l le st m ->
  exists lval : list val,
    map_opt (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)
      l' = Some lval.
Proof.
  induction l'.
  - simpl.
    intros. exists nil.
    reflexivity.
  - intros.
    simpl.
    assert (In a (List.map fst l)).
    apply H. simpl. tauto.
    apply List.incl_cons_inv in H.
    destruct H as (IN & INCL).
    assert (H0':= H0).
    eapply IHl' in H0'; eauto.
    destruct H0'.
    unfold match_temp_env in H0.
    rewrite Forall_forall in H0.
    rewrite in_map_iff in IN.
    destruct IN as (v' & FST & IN).
    subst. apply H0 in IN.
    unfold match_elt in IN.
    unfold AST.ident in *.
    destruct (Maps.PTree.get (fst (fst v')) le); try tauto.
    rewrite H.
    eexists. reflexivity.
Qed.