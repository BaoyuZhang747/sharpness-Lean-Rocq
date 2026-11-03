From mathcomp Require Import all_boot.
From DiazPark Require Import Category.

(** Finite coproducts of representables representing a product.
    The factorization is through a literal finite family of actual spans.
    Both its index and its apex arrow are uniquely determined. This is an
    interface for the universal property, not an assertion that an arbitrary
    category has such decompositions. *)

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record finite_product_decomposition (C : category) (P Q : C) := {
  fp_index : finType;
  fp_apex : fp_index -> C;
  fp_left : forall i, hom C (fp_apex i) P;
  fp_right : forall i, hom C (fp_apex i) Q;
  fp_lift : forall X, hom C X P -> hom C X Q ->
    {i : fp_index & hom C X (fp_apex i)};
  fp_lift_left : forall X (f : hom C X P) (g : hom C X Q),
    compose (projT2 (@fp_lift X f g))
      (fp_left (projT1 (@fp_lift X f g))) = f;
  fp_lift_right : forall X (f : hom C X P) (g : hom C X Q),
    compose (projT2 (@fp_lift X f g))
      (fp_right (projT1 (@fp_lift X f g))) = g;
  fp_unique : forall X i (h : hom C X (fp_apex i)),
    @fp_lift X (compose h (fp_left i)) (compose h (fp_right i)) =
      existT (fun j => hom C X (fp_apex j)) i h
}.

Arguments fp_index {_ _ _} _.
Arguments fp_apex {_ _ _} _ _.
Arguments fp_left {_ _ _} _ _.
Arguments fp_right {_ _ _} _ _.
Arguments fp_lift {_ _ _} _ {_} _ _.
Arguments fp_lift_left {_ _ _} _ {_} _ _.
Arguments fp_lift_right {_ _ _} _ {_} _ _.
Arguments fp_unique {_ _ _} _ {_} _ _.

Definition fp_factors {C : category} {P Q : C}
    (D : finite_product_decomposition P Q) (X : C) :=
  {i : fp_index D & hom C X (fp_apex D i)}.

Definition fp_encode {C : category} {P Q X : C}
    (D : finite_product_decomposition P Q) (t : fp_factors D X) :
    (hom C X P * hom C X Q)%type :=
  (compose (projT2 t) (fp_left D (projT1 t)),
   compose (projT2 t) (fp_right D (projT1 t))).

Arguments fp_encode {_ _ _ _} _ _.

Lemma fp_encode_lift {C : category} {P Q X : C}
    (D : finite_product_decomposition P Q)
    (f : hom C X P) (g : hom C X Q) :
    fp_encode D (fp_lift D f g) = (f, g).
Proof. unfold fp_encode; rewrite fp_lift_left fp_lift_right; reflexivity. Qed.

Lemma fp_factor_unique {C : category} {P Q X : C}
    (D : finite_product_decomposition P Q)
    (f : hom C X P) (g : hom C X Q) (t : fp_factors D X) :
    fp_encode D t = (f, g) -> t = fp_lift D f g.
Proof.
destruct t as [i h]; intro ht.
pose proof (f_equal fst ht) as hf.
pose proof (f_equal snd ht) as hg.
cbn in hf, hg; symmetry; rewrite <- hf, <- hg.
apply fp_unique.
Qed.

Arguments fp_factor_unique {_ _ _ _} _ {_ _ _} _.

Lemma fp_encode_injective {C : category} {P Q X : C}
    (D : finite_product_decomposition P Q) :
    injective (@fp_encode C P Q X D).
Proof.
intros t u h; destruct (fp_encode D u) as [f g] eqn:hu.
rewrite (fp_factor_unique D h) (fp_factor_unique D hu); reflexivity.
Qed.

Lemma fp_encode_surjective {C : category} {P Q X : C}
    (D : finite_product_decomposition P Q)
    (a : (hom C X P * hom C X Q)%type) :
    exists t : fp_factors D X, fp_encode D t = a.
Proof. destruct a as [f g]; exists (fp_lift D f g); apply fp_encode_lift. Qed.

Definition fp_precompose {C : category} {P Q X Y : C}
    (D : finite_product_decomposition P Q) (h : hom C Y X)
    (t : fp_factors D X) : fp_factors D Y :=
  match t with
  | existT i k => existT (fun j => hom C Y (fp_apex D j)) i (compose h k)
  end.

Arguments fp_precompose {_ _ _ _ _} _ _ _.

Lemma fp_encode_precompose {C : category} {P Q X Y : C}
    (D : finite_product_decomposition P Q) (h : hom C Y X)
    (t : fp_factors D X) :
    fp_encode D (fp_precompose D h t) =
      (compose h (fst (fp_encode D t)), compose h (snd (fp_encode D t))).
Proof.
destruct t as [i k]; unfold fp_encode, fp_precompose; cbn.
rewrite !compose_assoc; reflexivity.
Qed.

Lemma fp_lift_precompose {C : category} {P Q X Y : C}
    (D : finite_product_decomposition P Q) (h : hom C Y X)
    (f : hom C X P) (g : hom C X Q) :
    fp_precompose D h (fp_lift D f g) =
      fp_lift D (compose h f) (compose h g).
Proof.
apply fp_encode_injective.
rewrite fp_encode_precompose !fp_encode_lift; reflexivity.
Qed.

Definition fp_swap {C : category} {P Q : C}
    (D : finite_product_decomposition P Q) : finite_product_decomposition Q P.
Proof.
refine {| fp_index := fp_index D;
          fp_apex := fp_apex D;
          fp_left := fp_right D;
          fp_right := fp_left D;
          fp_lift := fun X f g => fp_lift D g f |}.
- intros X f g; apply fp_lift_right.
- intros X f g; apply fp_lift_left.
- intros X i h; apply fp_unique.
Defined.

Print Assumptions fp_factor_unique.
Print Assumptions fp_encode_injective.
Print Assumptions fp_lift_precompose.
Print Assumptions fp_swap.
