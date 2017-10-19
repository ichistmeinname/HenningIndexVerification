Require Import List.
Require Import FunctionalExtensionality.
Import ListNotations.
Import Coq.Program.Basics.

Set Implicit Arguments.

Inductive BDD :=
| Zero : BDD
| One : BDD
(* label ; id ; t ; e *)
| Node : nat -> nat -> BDD -> BDD -> BDD
| Ref : nat -> BDD.


Definition mapFirst A B C (f : A -> B) (p : A * C) :=
  pair (f (fst p)) (snd p).

Definition mapSecond A B C (f : A -> B) (p : C * A) :=
  pair (fst p) (f (snd p)).


Section Algebra.

  Variable A : Type.
  Variable one : A.
  Variable zero : A.
  Variable plus : A -> A -> A.
  Variable mult : A -> A -> A.

  Variable mult_1_r : forall x, mult x one = x.
  Variable mult_1_l : forall x, mult zero x = x.
  Variable plus_0_r : forall x, plus x zero = x.
  Variable plus_0_l : forall x, plus zero x = x.
  Variable mult_0_r : forall x, mult x zero = zero.
  Variable plus_assoc : forall z1 z2 z3, plus z1 (plus z2 z3) = plus (plus z1 z2) z3.
  Variable mult_assoc : forall z1 z2 z3, mult z1 (mult z2 z3) = mult (mult z1 z2) z3.
  Variable mult_comm : forall x y, mult x y = mult y x.
  Variable mult_plus_distr : forall x y z, mult x (plus y z) = plus (mult x y) (mult x z).

  Variable f : nat -> A.
  Variable g : nat -> A.
  
  Definition sum : list A -> A := fold_right plus zero.

  Definition prod : list A -> A := fold_right mult one.

  Definition prods (pair : list nat * list nat) :=
    mult (prod (map f (fst pair))) (prod (map g (snd pair))).

  Definition h (xs : list (list nat * list nat)) : A := sum (map prods xs).

  Definition p (v : list (list nat * list nat)) (z : nat) (w : list (list nat * list nat)) :=
    map (mapFirst (fun zs => z :: zs)) v
        ++ map (mapSecond (fun zs => z :: zs)) w.

  Definition q (pt : A) (v : nat) (pe : A) :=
    plus (mult (f v) pt) (mult (g v) pe).

  Definition x : list (list nat * list nat) := [].
  Definition y : list (list nat * list nat) := [([],[])].

  Section Proof_Obligations.
    
    Lemma h_x_zero :
      h x = zero.
    Proof.
      unfold h, x.
      reflexivity.
    Qed.

    Lemma h_y_one :
      h y = one.
    Proof.
      unfold h, y; simpl.
      unfold prods; simpl.
      rewrite mult_1_r.
      apply plus_0_r.
    Qed.

 
    Lemma sum_homomorphism :
      forall (xs ys : list A),
        sum (xs ++ ys) = plus (sum xs) (sum ys).
    Proof.
      intros xs ys.
      revert ys.
      induction xs; intro ys.
      - unfold "++".
        rewrite <- plus_0_l with (x := (sum ys)) at 1.
        simpl.
        reflexivity.
      - simpl sum.
        rewrite IHxs.
        rewrite plus_assoc.
        reflexivity.
    Qed.

    (* Lemma prod_map_append : *)
    (*   forall B (xs ys : list B) (h1 h2 : B -> A), *)
    (*     (forall z1 z2 z3, mult z1 (mult z2 z3) = mult (mult z1 z2) z3) -> *)
    (*     prod (map h1 xs ++ map h2 ys) = mult (prod (map h1 xs)) (prod (map h2 ys)). *)
    (* Proof. *)
    (*   intros B xs ys h1 h2 mult_assoc. *)
    (*   revert ys. *)
    (*   induction xs; intro ys; destruct ys; simpl. *)
    (*   - rewrite one_rn_mult. *)
    (*     reflexivity. *)
    (*   - rewrite zero_ln_plus. *)
    (*     reflexivity. *)
    (*   - rewrite app_nil_r. *)
    (*     rewrite zero_rn_plus. *)
    (*     reflexivity. *)
    (*   - specialize (IHxs (b :: ys)). *)
    (*     simpl in *. *)
    (*     rewrite IHxs. *)
    (*     rewrite plus_assoc. *)
    (*     reflexivity. *)
    (* Qed. *)

    Lemma mult_prod_map :
      forall B C (z : B) (h1 : B -> A) (zsc : list B * C),
        mult (h1 z) (prod (map h1 (fst zsc))) = prod (map h1 (z :: fst zsc)).
    Proof.
      reflexivity.
    Qed.

    Lemma mult_sum :
      forall c l, mult c (sum l) = sum (map (mult c) l).
    Proof.
      intros c l.
      induction l.
      - simpl sum.
        apply mult_0_r.
      - simpl sum.
        rewrite mult_plus_distr.
        rewrite IHl.
        reflexivity.
    Qed.

    Lemma prods_cons1 :
      forall l z,
        prods (mapFirst (fun zs => z :: zs) l) = mult (f z) (prods l).
    Proof.
      intros l z.
      unfold prods.
      simpl.
      rewrite mult_assoc.
      reflexivity.
    Qed.

    Lemma prods_cons2 :
      forall l z,
        prods (mapSecond (fun zs => z :: zs) l) = mult (g z) (prods l).
    Proof.
      intros l z.
      unfold prods.
      simpl.
      rewrite mult_assoc, mult_comm with (x := prod (map f (fst l))), <- mult_assoc.
      reflexivity.
    Qed.

    Lemma h_p_q_paper_version :
      forall v n w,
        h (p v n w) = q (h v) n (h w).
    Proof.
      intros v n w.
      unfold h at 1.
      unfold p.
      rewrite map_app.
      do 2 rewrite map_map.
      rewrite sum_homomorphism.
      
      replace (fun x0 : list nat * list nat => prods (mapFirst (fun zs => n :: zs) x0))
      with (fun x0 : list nat * list nat => mult (f n) (prods x0));
        try (extensionality xys; rewrite prods_cons1; reflexivity).

      replace (fun x0 : list nat * list nat => prods (mapSecond (fun zs => n :: zs) x0))
      with (fun x0 : list nat * list nat => mult (g n) (prods x0));
        try (extensionality xys; rewrite prods_cons2; reflexivity).

      rewrite <- map_map.
      rewrite <- mult_sum.
      rewrite <- map_map with (l := w).
      rewrite <- mult_sum.

      unfold q.
      unfold h.
      reflexivity.
    Qed.

    Lemma h_p_q :
      forall v n w,
        h (p v n w) = q (h v) n (h w).
    Proof.
      intros v n w.
      unfold h at 1.
      unfold p.
      rewrite map_app.
      do 2 rewrite map_map.
      rewrite sum_homomorphism.

      unfold q.
      unfold h.
      do 2 rewrite mult_sum.
      do 2 rewrite map_map.
      unfold prods.
      simpl fst; simpl snd; simpl prod.

      do 3 f_equal.
      - extensionality pair.
        rewrite <- mult_assoc.
        reflexivity.
      - extensionality pair.
        rewrite mult_assoc.
        rewrite mult_comm with (x := prod (map f (fst pair))).
        rewrite <- mult_assoc.
        reflexivity.
    Qed.

  End Proof_Obligations.
End Algebra.