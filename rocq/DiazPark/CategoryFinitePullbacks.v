From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryComma CategoryFiniteProducts.

(** A finite pullback is a disjoint finite family of actual commuting spans.
    We construct its product in the actual slice category. The only classical
    selection is of the uniquely determined lifting pair (index, arrow). *)

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record finite_pullback_decomposition (C : category) (P Q T : C)
    (f : hom C P T) (g : hom C Q T) := {
  pb_index : finType;
  pb_apex : pb_index -> C;
  pb_left : forall i, hom C (pb_apex i) P;
  pb_right : forall i, hom C (pb_apex i) Q;
  pb_commutes : forall i, compose (pb_left i) f = compose (pb_right i) g;
  pb_exists : forall X (a : hom C X P) (b : hom C X Q),
    compose a f = compose b g ->
    exists t : {i : pb_index & hom C X (pb_apex i)},
      compose (projT2 t) (pb_left (projT1 t)) = a /\
      compose (projT2 t) (pb_right (projT1 t)) = b;
  pb_unique : forall X (t u : {i : pb_index & hom C X (pb_apex i)}),
    compose (projT2 t) (pb_left (projT1 t)) =
      compose (projT2 u) (pb_left (projT1 u)) ->
    compose (projT2 t) (pb_right (projT1 t)) =
      compose (projT2 u) (pb_right (projT1 u)) -> t = u
}.

Arguments pb_index {_ _ _ _ _ _} _.
Arguments pb_apex {_ _ _ _ _ _} _ _.
Arguments pb_left {_ _ _ _ _ _} _ _.
Arguments pb_right {_ _ _ _ _ _} _ _.
Arguments pb_commutes {_ _ _ _ _ _} _ _.
Arguments pb_exists {_ _ _ _ _ _} _ {_} _ _ _.
Arguments pb_unique {_ _ _ _ _ _} _ {_} _ _ _ _.

Definition over_object {C : category} {P T : C} (f : hom C P T) :
    over_category C T :=
  @Build_costructured_object C C (functor_id C) T P f.

Arguments over_object {_ _ _} _.

Section SliceProduct.
Context {C : category} {P Q T : C} {f : hom C P T} {g : hom C Q T}.
Variable D : finite_pullback_decomposition f g.

Definition pb_slice_apex (i : pb_index D) : over_category C T :=
  over_object (compose (pb_left D i) f).

Definition pb_slice_left (i : pb_index D) :
    hom (over_category C T) (pb_slice_apex i) (over_object f).
Proof.
refine (@Build_costructured_hom C C (functor_id C) T
  (pb_slice_apex i) (over_object f) (pb_left D i) _).
reflexivity.
Defined.

Definition pb_slice_right (i : pb_index D) :
    hom (over_category C T) (pb_slice_apex i) (over_object g).
Proof.
refine (@Build_costructured_hom C C (functor_id C) T
  (pb_slice_apex i) (over_object g) (pb_right D i) _).
symmetry; apply pb_commutes.
Defined.

Definition pb_slice_forget {X : over_category C T}
    (t : {i : pb_index D & hom (over_category C T) X (pb_slice_apex i)}) :
    {i : pb_index D & hom C (costructured_source X) (pb_apex D i)} :=
  existT _ (projT1 t) (costructured_map (projT2 t)).

Lemma pb_slice_forget_injective {X : over_category C T} :
    injective (@pb_slice_forget X).
Proof.
intros [i h] [j k] e.
pose proof (existT_inj1 e) as eij; simpl in eij; destruct eij.
pose proof (existT_inj2 e) as ehk.
f_equal; apply costructured_hom_ext; exact ehk.
Qed.

Lemma pb_slice_exists (X : over_category C T)
    (a : hom (over_category C T) X (over_object f))
    (b : hom (over_category C T) X (over_object g)) :
    exists t : {i : pb_index D & hom (over_category C T) X (pb_slice_apex i)},
      compose (projT2 t) (pb_slice_left (projT1 t)) = a /\
      compose (projT2 t) (pb_slice_right (projT1 t)) = b.
Proof.
have hc : compose (costructured_map a) f = compose (costructured_map b) g.
  transitivity (costructured_arrow X).
  - exact (costructured_commutes a).
  - symmetry; exact (costructured_commutes b).
destruct (pb_exists D (costructured_map a) (costructured_map b) hc)
  as [[i h] [ha hb]]; simpl in ha, hb.
have hh : compose h (compose (pb_left D i) f) = costructured_arrow X.
  rewrite <- compose_assoc, ha; exact (costructured_commutes a).
pose k := @Build_costructured_hom C C (functor_id C) T X
  (pb_slice_apex i) h hh.
exists (existT _ i k); split; apply costructured_hom_ext; assumption.
Qed.

Definition pb_slice_lift {X : over_category C T}
    (a : hom (over_category C T) X (over_object f))
    (b : hom (over_category C T) X (over_object g)) :=
  proj1_sig (cid (pb_slice_exists a b)).

Lemma pb_slice_lift_left {X : over_category C T}
    (a : hom (over_category C T) X (over_object f))
    (b : hom (over_category C T) X (over_object g)) :
    compose (projT2 (pb_slice_lift a b))
      (pb_slice_left (projT1 (pb_slice_lift a b))) = a.
Proof. exact (proj1 (proj2_sig (cid (pb_slice_exists a b)))). Qed.

Lemma pb_slice_lift_right {X : over_category C T}
    (a : hom (over_category C T) X (over_object f))
    (b : hom (over_category C T) X (over_object g)) :
    compose (projT2 (pb_slice_lift a b))
      (pb_slice_right (projT1 (pb_slice_lift a b))) = b.
Proof. exact (proj2 (proj2_sig (cid (pb_slice_exists a b)))). Qed.

Lemma pb_slice_lift_unique {X : over_category C T} (i : pb_index D)
    (h : hom (over_category C T) X (pb_slice_apex i)) :
    pb_slice_lift (compose h (pb_slice_left i)) (compose h (pb_slice_right i)) =
      existT (fun j => hom (over_category C T) X (pb_slice_apex j)) i h.
Proof.
apply pb_slice_forget_injective; apply pb_unique.
- exact (f_equal (@costructured_map C C (functor_id C) T X (over_object f))
    (pb_slice_lift_left (compose h (pb_slice_left i)) (compose h (pb_slice_right i)))).
- exact (f_equal (@costructured_map C C (functor_id C) T X (over_object g))
    (pb_slice_lift_right (compose h (pb_slice_left i)) (compose h (pb_slice_right i)))).
Qed.

Definition pb_slice_product :
    finite_product_decomposition (over_object f) (over_object g) :=
  {| fp_index := pb_index D;
     fp_apex := pb_slice_apex;
     fp_left := pb_slice_left;
     fp_right := pb_slice_right;
     fp_lift := @pb_slice_lift;
     fp_lift_left := @pb_slice_lift_left;
     fp_lift_right := @pb_slice_lift_right;
     fp_unique := @pb_slice_lift_unique |}.

End SliceProduct.

Print Assumptions pb_slice_product.
Print Assumptions pb_slice_forget_injective.
