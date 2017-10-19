Require Import List.
Import ListNotations.
Require Import PeanoNat.
(* Import Nat. *)
Require Import Ring.
(* Require Import Arith. *)
(* Import ArithRing. *)
(* Require Import NArithRing. *)
(* Require Import NArith. *)
Require Import FunctionalExtensionality.
Require Import BinInt.
Require Import ZArith.
Require Import ZArithRing.
Import Z.
Open Scope Z_scope.

Set Implicit Arguments.

Definition Vector (A : Type) := list A.


(* Vector functions *)

Fixpoint alignWith (A : Type) (f : A -> A -> A) (v1 v2 : Vector A) :=
  match v1, v2 with
  | [], _ => v2
  | _, [] => v1
  | a1 :: v12, a2 :: v22 => f a1 a2 :: alignWith f v12 v22
  end.


(* Laws about Vector functions *)

Lemma map_alignWith :
  forall A (f : A -> A -> A) (g : A -> A),
      (forall (x y : A), g (f x y) = f (g x) (g y)) ->
      forall (v1 v2 : Vector A), map g (alignWith f v1 v2) = alignWith f (map g v1) (map g v2).
Proof.
  induction v1; destruct v2; simpl alignWith; simpl map; try reflexivity; rewrite H; rewrite IHv1; reflexivity.
Qed.


(* Addition *)

Definition zero : Vector Z := [].

Definition plus (v1 v2 : Vector Z) : Vector Z :=
  alignWith add v1 v2.

Hint Unfold plus.
Ltac simpl_plus := unfold plus; simpl alignWith.

(* Auxiliary lemmas *)

Lemma map_plus :
  forall (n : Z) (v1 v2 : Vector Z),
    map (mul n) (plus v1 v2) = plus (map (mul n) v1) (map (mul n) v2).
Proof.
  intros n v1 v2; unfold plus.
  rewrite map_alignWith; try reflexivity.
  apply mul_add_distr_l.
Qed.

Lemma plus_cons :
  forall (n1 n2 : Z) (v1 v2 : Vector Z),
    n1 + n2 :: plus v1 v2 = plus (n1 :: v1) (n2 :: v2).
Proof.
  reflexivity.
Qed.


(* Properties of plus *)

Lemma plus_comm :
  forall (v1 v2 : Vector Z),
    plus v1 v2 = plus v2 v1.
Proof.
  induction v1; destruct v2;
    simpl_plus; try reflexivity; rewrite add_comm;
      rewrite <- IHv1; reflexivity.
Qed.

Lemma plus_0_l :
  forall (v : Vector Z),
    plus zero v = v.
Proof.
  unfold zero, plus.
  simpl alignWith.
  reflexivity.
Qed.

Lemma plus_0_r :
  forall (v : Vector Z),
    plus v zero = v.
Proof.
  intro v.
  rewrite plus_comm.
  apply plus_0_l.
Qed.

Lemma plus_assoc :
  forall (v1 v2 v3 : Vector Z),
    plus v1 (plus v2 v3) = plus (plus v1 v2) v3.
Proof.
  induction v1; destruct v2, v3; try reflexivity;
    simpl_plus; simpl alignWith; rewrite IHv1, add_assoc; reflexivity.
Qed.


(* Derived lemmas about plus *)

Lemma plus_swap_1 :
  forall (v1 v2 v3 : Vector Z),
    plus v1 (plus v2 v3) = plus v2 (plus v1 v3).
Proof.
  intros v1 v2 v3.
  rewrite plus_assoc, plus_comm with (v1 := v1), <- plus_assoc.
  reflexivity.
Qed.

Lemma plus_swap_2 :
  forall (v1 v2 v3 v4 : Vector Z),
    plus (plus v1 v2) (plus v3 v4) = plus (plus v1 v3) (plus v2 v4).
Proof.
  intros v1 v2 v3 v4.
  rewrite plus_assoc, <- plus_assoc with (v1 := v1), plus_comm with (v1 := v2), plus_assoc, plus_assoc.
  reflexivity.
Qed.


Definition one : Vector Z := [1].

Fixpoint mult (v1 v2 : Vector Z) : Vector Z :=
  match v1, v2 with
  | [], _ => []
  | _, [] => []
  | n :: v12, _ => plus (map (mul n) v2) (0 :: mult v12 v2)
  end.


(* Auxiliary lemmas about mult *)

Lemma map_mult :
  forall (n : Z) (v1 v2 : Vector Z),
    map (mul n) (mult v1 v2) = mult (map (mul n) v1) v2.
Proof.
  intros v.
  induction v1; intros v2; simpl mult; try reflexivity.
  destruct v2; try reflexivity.
  rewrite map_plus, map_map, <- IHv1.
  simpl map.
  rewrite mul_0_r.
  do 2 f_equal.
  - ring.
  - f_equal.
    extensionality x.
    ring.
Qed.


Lemma map_add_0 :
  forall (v : Vector Z), map (fun n => n + 0) v = v.
Proof.
  induction v; simpl; try reflexivity.
  rewrite add_0_r, IHv.
  reflexivity.
Qed.


(* Properties of mult *)

Lemma mult_comm :
  forall (v1 v2 : Vector Z),
    mult v1 v2 = mult v2 v1.
Proof.
  induction v1; induction v2; simpl; try reflexivity.
  rewrite <- IHv2, IHv1.
  do 2 rewrite <- plus_cons.
  f_equal.
  - ring.
  - simpl.
    destruct v1, v2; only 1-3: simpl; try reflexivity.
    + rewrite plus_0_r, plus_0_l.
      simpl_plus.
      rewrite plus_0_r, add_0_r.
      reflexivity.
    + rewrite plus_0_l, plus_0_r.
      simpl_plus.
      rewrite plus_0_r, add_0_r.
      reflexivity.
    + rewrite plus_swap_1. rewrite <- IHv1.
      reflexivity.
Qed.

Lemma mult_0_l :
  forall (v : Vector Z),
    mult zero v = zero.
Proof.
  reflexivity.
Qed.

Lemma mult_0_r :
  forall (v : Vector Z),
    mult v zero =  zero.
Proof.
  intros v1.
  rewrite mult_comm, mult_0_l.
  reflexivity.
Qed.

Lemma alignWith_nil_r :
  forall A (f : A -> A -> A) v, alignWith f v [] = v.
Proof.
  intros A f v.
  induction v; reflexivity.
Qed.

Lemma mult_1_l :
  forall (v : Vector Z),
    mult one v = v.
Proof.
  intros v.
  unfold one.
  destruct v; simpl; try reflexivity.
  simpl_plus.
  rewrite alignWith_nil_r.
  rewrite map_ext with (g := id); try (intros; unfold id; ring).
  rewrite map_id.
  destruct z; try reflexivity.
Qed.

Lemma mult_1_r :
  forall (v : Vector Z),
    mult v one = v.
Proof.
  intros v.
  rewrite mult_comm.
  apply mult_1_l.
Qed.


(* Auxiliary lemma for proving associativity and distributivity *)

Lemma mult_plus_distr_r :
  forall (v1 v2 v3 : Vector Z),
    mult v1 (plus v2 v3) = plus (mult v1 v2) (mult v1 v3).
Proof.
  induction v1; intros v2 v3; simpl mult; try reflexivity.
  destruct v2.
  - rewrite plus_0_l.
    destruct v3; try reflexivity.
  - destruct v3.
    + rewrite plus_0_r.
      reflexivity.
    + unfold plus.
      simpl.
      ring_simplify (a * (z + z0) + 0) (a * z + 0 + (a * z0 + 0)).
      rewrite map_plus.
      do 2 rewrite plus_cons.
      rewrite IHv1.
      rewrite plus_swap_2.
      reflexivity.
Qed.

Lemma mult_plus_distr_l :
  forall (v1 v2 v3 : Vector Z),
    mult (plus v1 v2) v3 = plus (mult v1 v3) (mult v2 v3).
Proof.
  intros v1 v2 v3.
  rewrite mult_comm, mult_plus_distr_r, mult_comm, (mult_comm v3).
  reflexivity.
Qed.

Lemma mult_assoc :
  forall (v1 v2 v3 : Vector Z),
    mult v1 (mult v2 v3) = mult (mult v1 v2) v3.
Proof.
  induction v1; intros v2 v3; simpl mult; try reflexivity.
  rewrite IHv1.
  destruct v2.
  - rewrite mult_0_l.
    reflexivity.
  - destruct v3; simpl; try reflexivity.
    rewrite <- plus_cons, <- plus_cons.
    f_equal.
    + ring.
    + rewrite mult_plus_distr_l, <- IHv1, plus_assoc.
      unfold plus.
      rewrite map_alignWith.
      * rewrite map_map, map_mult.
        do 3 f_equal.
        extensionality x.
        ring.
      * apply mul_add_distr_l.
Qed.
