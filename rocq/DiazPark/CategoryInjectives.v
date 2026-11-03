(** Injectivity is the usual extension property against every monomorphism.
    Preservation by right adjoints is proved from the unit and counit; it is
    not included as a field of the adjunction. No existence of enough
    injectives is asserted in this file. *)

From DiazPark Require Import Category CategoryAdjunction CategoryLimits.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition monomorphism {C : category} {x y : C} (m : hom C x y) : Prop :=
  forall (z : C) (f g : hom C z x), compose f m = compose g m -> f = g.

Definition injective_object (C : category) (i : C) : Prop :=
  forall (x y : C) (m : hom C x y), monomorphism m ->
    forall f : hom C x i, exists g : hom C y i, compose m g = f.

Arguments injective_object C i : clear implicits.

Definition preserves_monomorphisms {C D : category} (F : functor C D) : Prop :=
  forall (x y : C) (m : hom C x y), monomorphism m -> monomorphism (fmap F m).

Lemma identity_monomorphism {C : category} (x : C) :
    monomorphism (identity x).
Proof. intros z f g e. now rewrite !compose_id_right in e. Qed.

Lemma compose_monomorphism {C : category} {x y z : C}
    (f : hom C x y) (g : hom C y z) :
    monomorphism f -> monomorphism g -> monomorphism (compose f g).
Proof.
  intros hf hg w a b e. apply hf. apply hg.
  now rewrite !compose_assoc.
Qed.

Lemma retract_monomorphism {C : category} {x y : C}
    (s : hom C x y) (r : hom C y x) :
    compose s r = identity x -> monomorphism s.
Proof.
  intros sr z f g e.
  pose proof (f_equal (fun k => compose k r) e) as h.
  change (compose (compose f s) r = compose (compose g s) r) in h.
  now rewrite !compose_assoc, sr, !compose_id_right in h.
Qed.

Lemma injective_retract {C : category} {i j : C}
    (s : hom C i j) (r : hom C j i) :
    compose s r = identity i -> injective_object C j -> injective_object C i.
Proof.
  intros sr hj x y m hm f.
  destruct (hj x y m hm (compose f s)) as [g hg].
  exists (compose g r). rewrite <- compose_assoc, hg, compose_assoc, sr.
  apply compose_id_right.
Qed.

Lemma injective_isomorphism {C : category} {i j : C}
    (e : isomorphism i j) : injective_object C i -> injective_object C j.
Proof.
  intro hi. exact (injective_retract (iso_inv_hom e) hi).
Qed.

Section AdjunctionHom.
Context {C D : category} {L : functor C D} {R : functor D C}.
Variable a : adjunction L R.

Definition adjoint_to_right {x : C} {y : D}
    (f : hom D (fobj L x) y) : hom C x (fobj R y) :=
  compose (component (adj_unit a) x) (fmap R f).

Definition adjoint_to_left {x : C} {y : D}
    (f : hom C x (fobj R y)) : hom D (fobj L x) y :=
  compose (fmap L f) (component (adj_counit a) y).

Lemma adjoint_left_right {x : C} {y : D} (f : hom D (fobj L x) y) :
    adjoint_to_left (adjoint_to_right f) = f.
Proof.
  unfold adjoint_to_left, adjoint_to_right.
  rewrite fmap_compose, compose_assoc.
  pose proof (naturality (adj_counit a) f) as h.
  change (compose (fmap L (fmap R f)) (component (adj_counit a) y) =
    compose (component (adj_counit a) (fobj L x)) f) in h.
  transitivity (compose (fmap L (component (adj_unit a) x))
    (compose (component (adj_counit a) (fobj L x)) f)).
  - exact (f_equal (fun k => compose (fmap L (component (adj_unit a) x)) k) h).
  -
  rewrite <- compose_assoc, adj_triangle_left, compose_id_left.
  reflexivity.
Qed.

Lemma adjoint_right_left {x : C} {y : D} (f : hom C x (fobj R y)) :
    adjoint_to_right (adjoint_to_left f) = f.
Proof.
  unfold adjoint_to_left, adjoint_to_right.
  rewrite fmap_compose, <- compose_assoc.
  pose proof (naturality (adj_unit a) f) as h.
  change (compose f (component (adj_unit a) (fobj R y)) =
    compose (component (adj_unit a) x) (fmap R (fmap L f))) in h.
  rewrite <- h.
  rewrite compose_assoc.
  transitivity (compose f (identity (fobj R y))).
  - exact (f_equal (fun k => compose f k) (adj_triangle_right a y)).
  - apply compose_id_right.
Qed.

Lemma adjoint_to_right_precompose {x x' : C} {y : D}
    (m : hom C x' x) (f : hom D (fobj L x) y) :
    adjoint_to_right (compose (fmap L m) f) = compose m (adjoint_to_right f).
Proof.
  unfold adjoint_to_right. rewrite fmap_compose, <- compose_assoc.
  pose proof (naturality (adj_unit a) m) as h.
  change (compose m (component (adj_unit a) x) =
    compose (component (adj_unit a) x') (fmap R (fmap L m))) in h.
  rewrite <- h. apply compose_assoc.
Qed.

Lemma adjoint_to_left_precompose {x x' : C} {y : D}
    (m : hom C x' x) (f : hom C x (fobj R y)) :
    adjoint_to_left (compose m f) = compose (fmap L m) (adjoint_to_left f).
Proof. unfold adjoint_to_left. rewrite fmap_compose. apply compose_assoc. Qed.

Lemma adjoint_to_right_postcompose {x : C} {y y' : D}
    (f : hom D (fobj L x) y) (k : hom D y y') :
    adjoint_to_right (compose f k) = compose (adjoint_to_right f) (fmap R k).
Proof.
  unfold adjoint_to_right. rewrite fmap_compose. symmetry. apply compose_assoc.
Qed.

Lemma adjoint_to_left_postcompose {x : C} {y y' : D}
    (f : hom C x (fobj R y)) (k : hom D y y') :
    adjoint_to_left (compose f (fmap R k)) = compose (adjoint_to_left f) k.
Proof.
  unfold adjoint_to_left. rewrite fmap_compose, compose_assoc.
  pose proof (naturality (adj_counit a) k) as h.
  change (compose (fmap L (fmap R k)) (component (adj_counit a) y') =
    compose (component (adj_counit a) y) k) in h.
  rewrite h. symmetry. apply compose_assoc.
Qed.

(** Exactness of the left adjoint in the manuscript implies the weaker
    hypothesis used here: it takes every monomorphism to a monomorphism. *)
Theorem right_adjoint_preserves_injectives :
    preserves_monomorphisms L -> forall i : D,
    injective_object D i -> injective_object C (fobj R i).
Proof.
  intros hL i hi x y m hm f.
  destruct (hi (fobj L x) (fobj L y) (fmap L m) (hL x y m hm)
    (adjoint_to_left f)) as [g hg].
  exists (adjoint_to_right g).
  rewrite <- adjoint_to_right_precompose, hg. apply adjoint_right_left.
Qed.

End AdjunctionHom.
