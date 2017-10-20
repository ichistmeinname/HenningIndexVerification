Require Import List.
Require Import FunctionalExtensionality.
Import ListNotations.
Import Coq.Program.Basics.

Set Implicit Arguments.

Section Pair.

  Definition mapFirst A B C (f : A -> B) (p : A * C) :=
    pair (f (fst p)) (snd p).

  Definition mapSecond A B C (f : A -> B) (p : C * A) :=
    pair (fst p) (f (snd p)).

End Pair.

Section BDD.

  Inductive BDD :=
  | Zero : BDD
  | One : BDD
  | Node : nat -> nat -> BDD -> BDD -> BDD
  | Ref : nat -> BDD.

  Fixpoint foldBDD (A : Type) (zero one : A) (ref : nat -> A)
           (node : nat -> A -> nat -> A -> A) (bdd : BDD) : A :=
    match bdd with
    | Zero => zero
    | One  => one
    | Ref i => ref i
    | Node id var thenB elseB =>
      node id (foldBDD zero one ref node thenB)
           var (foldBDD zero one ref node elseB)
    end.

  Section Dict.

    Variable K V : Type.
    Definition Dict := K -> V.
    Definition insertDict (eqK : K -> K -> bool)
               (key : K) (val : V) (dict : Dict) : Dict :=
      fun k' => if eqK key k'
             then val
             else dict k'.

    Axiom ERROR : V.
    Definition emptyDict : Dict := fun k => ERROR.

  End Dict.

  Definition foldBDDShareDict (A : Type) (zero one : A)
           (node : A -> nat -> A -> A)
    : BDD -> Dict nat A -> Dict nat A * A :=
    let zeroS := fun dict => (dict, zero) in
    let oneS  := fun dict => (dict, one) in
    let refS  := fun i dict => (dict, dict i) in
    let nodeS := fun id thenF var elseF dict =>
        let '(dict1, res1) := thenF dict in
        let '(dict2, res2) := elseF dict1 in
        let res           := node res1 var res2
        in (insertDict Nat.eqb id res dict2, res)
    in foldBDD zeroS oneS refS nodeS.

  Definition foldBDDShare (A : Type) (zero one : A) (node : A -> nat -> A -> A)
             (bdd : BDD) : A :=
    snd (foldBDDShareDict zero one node bdd (@emptyDict nat A)).

  Definition all (bdd : BDD) : list (list nat * list nat) :=
    let nodeAll pt v pe :=
        map (mapFirst (fun xs => v :: xs)) pt
            ++ map (mapSecond (fun xs => v :: xs)) pe
    in foldBDDShare [] [([],[])] nodeAll bdd.

End BDD.

Section CommutativeSemiring.

  Class CommutativeSemiring (A : Type) :=
    { one : A;
      zero : A;
      plus : A -> A -> A;
      mult : A -> A -> A;
      plus_0_r : forall x, plus x zero = x;
      plus_0_l : forall x, plus zero x = x;
      plus_assoc : forall z1 z2 z3, plus z1 (plus z2 z3) = plus (plus z1 z2) z3;
      mult_1_r : forall x, mult x one = x;
      mult_1_l : forall x, mult zero x = x;
      mult_0_r : forall x, mult x zero = zero;
      mult_assoc : forall z1 z2 z3, mult z1 (mult z2 z3) = mult (mult z1 z2) z3;
      mult_comm : forall x y, mult x y = mult y x;
      mult_plus_distr : forall x y z, mult x (plus y z) = plus (mult x y) (mult x z)
    }.

  Variable A : Type.
  Context {CA : CommutativeSemiring A}.

  Definition sum : list A -> A := fold_right plus zero.

  Definition prod : list A -> A := fold_right mult one.

  Lemma mult_prod_map :
    forall B C (z : B) (h1 : B -> A) (zsc : list B * C),
      mult (h1 z) (prod (map h1 (fst zsc))) = prod (map h1 (z :: fst zsc)).
  Proof.
      reflexivity.
  Qed.

End CommutativeSemiring.

Section HenningIndex.

  Definition sumProdSpec (A : Type) `{CommutativeSemiring A}
             (f g : nat -> A) (bdd : BDD) : A :=
    let prods := fun '(win,comp) =>
        mult (prod (map f win)) (prod (map g comp))
    in sum (map prods (all bdd)).

  Definition sumProd (A : Type) {CA : CommutativeSemiring A}
             (f g : nat -> A) (bdd : BDD) : A :=
    let nodeSumProd t v e := plus (mult (f v) t) (mult (g v) e)
    in foldBDDShare zero one nodeSumProd bdd.

Section Lemma1.

  Variable A B : Type.
  Variable h : A -> B.
  Variable p : A -> nat -> A -> A.
  Variable q : B -> nat -> B -> B.

  Axiom free_theorem_foldBDDShare :
    (forall (v : A) (n : nat) (w : A),
        h (p v n w) = q (h v) n (h w)) ->
    forall (x y : A) (bdd : BDD),
      h (foldBDDShare x y p bdd) = foldBDDShare (h x) (h y) q bdd.

End Lemma1.

Section Lemma2.

  Variable A : Type.
  Context {CA : CommutativeSemiring A}.

  Lemma sum_homomorphism :
    forall (xs ys : list A),
      sum (xs ++ ys) = plus (sum xs) (sum ys).
  Proof.
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

End Lemma2.

Section Lemma3.

  Variable A : Type.
  Context {CA : CommutativeSemiring A}.

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

End Lemma3.

Section prods.

  Variable A : Type.
  Context {CA : CommutativeSemiring A}.

  Variable f : nat -> A.
  Variable g : nat -> A.

  Definition prods : list nat * list nat -> A :=
    fun '(win,comp) => mult (prod (map f win)) (prod (map g comp)).

End prods.

Section Lemma4.

  Variable A : Type.
  Context {CA : CommutativeSemiring A}.

  Variable f : nat -> A.
  Variable g : nat -> A.

  Lemma prods_cons1 :
    forall l z,
      prods f g (mapFirst (fun zs => z :: zs) l) = mult (f z) (prods f g l).
  Proof.
    intros l z.
    unfold prods.
    simpl.
    destruct l.
    rewrite mult_assoc.
    reflexivity.
  Qed.

End Lemma4.

Section Lemma5.

  Variable A : Type.
  Context {CA : CommutativeSemiring A}.

  Variable f : nat -> A.
  Variable g : nat -> A.

  Lemma prods_cons2 :
    forall l z,
      prods f g (mapSecond (fun zs => z :: zs) l) = mult (g z) (prods f g l).
  Proof.
    intros l z.
    unfold prods.
    destruct l.
    simpl.
    rewrite mult_assoc, mult_comm with (x := prod (map f l)), <- mult_assoc.
    reflexivity.
  Qed.

End Lemma5.

Section Theorem1.

  Variable A : Type.
  Context {CA : CommutativeSemiring A}.

  Variable f : nat -> A.
  Variable g : nat -> A.

  Definition prods' := prods f g.

  Definition h (xs : list (list nat * list nat)) : A := sum (map prods' xs).

  Definition p (v : list (list nat * list nat))
             (z : nat) (w : list (list nat * list nat)) :=
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
      unfold prods', prods; simpl.
      rewrite mult_1_r.
      apply plus_0_r.
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

      replace (fun x0 : list nat * list nat => prods' (mapFirst (fun zs => n :: zs) x0))
      with (fun x0 : list nat * list nat => mult (f n) (prods' x0));
        try (extensionality xys; unfold prods'; rewrite prods_cons1; reflexivity).

      replace (fun x0 : list nat * list nat => prods' (mapSecond (fun zs => n :: zs) x0))
      with (fun x0 : list nat * list nat => mult (g n) (prods' x0));
        try (extensionality xys; unfold prods'; rewrite prods_cons2; reflexivity).

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
      unfold prods', prods.
      simpl fst; simpl snd; simpl prod.

      do 3 f_equal.
      - extensionality pair.
        simpl.
        destruct pair.
        rewrite <- mult_assoc.
        reflexivity.
      - extensionality pair.
        simpl.
        destruct pair.
        rewrite mult_assoc.
        rewrite mult_comm with (x := prod (map f l)).
        rewrite <- mult_assoc.
        reflexivity.
    Qed.

  End Proof_Obligations.

  Theorem sumProd_sumProdSpec :
    forall bdd,
      sumProd f g bdd = sumProdSpec f g bdd.
    intro bdd.
    unfold sumProdSpec.
    unfold all.
    fold p.
    fold y.
    fold x.
    rewrite free_theorem_foldBDDShare
    with (h := fun xs => sum (map (fun '(win, comp) =>
                           mult (prod (map f win)) (prod (map g comp))) xs))
           (x := [])
           (y := [([],[])])
           (p := fun pt v pe => map (mapFirst (fun xs => v :: xs)) pt
                                 ++ map (mapSecond (fun xs => v :: xs)) pe)
           (q := fun pt v pe => plus (mult (f v) pt) (mult (g v) pe));
      try apply h_p_q.
    pose proof h_x_zero as Hzero.
    pose proof h_y_one as Hone.
    unfold h, prods', prods, x, y in *.
    rewrite Hzero.
    rewrite Hone.
    reflexivity.
  Qed.

End Theorem1.