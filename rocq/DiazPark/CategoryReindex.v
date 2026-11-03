From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryIsomorphism.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition hom_transport {C : category} {x y x' y' : C}
    (hx : x = x') (hy : y = y') (f : hom C x y) : hom C x' y' :=
  match hx, hy with eq_refl, eq_refl => f end.

Lemma hom_transport_identity {C : category} {x y : C} (h : x = y) :
  hom_transport h h (identity x) = identity y.
Proof. destruct h; reflexivity. Qed.

Lemma hom_transport_compose {C : category} {x y z x' y' z' : C}
    (hx : x = x') (hy : y = y') (hz : z = z')
    (f : hom C x y) (g : hom C y z) :
  hom_transport hx hz (compose f g) =
    compose (hom_transport hx hy f) (hom_transport hy hz g).
Proof. destruct hx, hy, hz; reflexivity. Qed.

Lemma hom_transport_twice {C : category} {x y x' y' x'' y'' : C}
    (hx : x = x') (hy : y = y') (kx : x' = x'') (ky : y' = y'')
    (f : hom C x y) :
  hom_transport kx ky (hom_transport hx hy f) =
    hom_transport (eq_trans hx kx) (eq_trans hy ky) f.
Proof. destruct hx, hy, kx, ky; reflexivity. Qed.

Lemma hom_transport_loop {C : category} {x y : C}
    (hx : x = x) (hy : y = y) (f : hom C x y) :
  hom_transport hx hy f = f.
Proof.
  replace hx with (Logic.eq_refl x) by apply Prop_irrelevance.
  replace hy with (Logic.eq_refl y) by apply Prop_irrelevance.
  reflexivity.
Qed.

Lemma functor_ext_pointwise {C D : category} (F G : functor C D)
    (ho : forall x, fobj F x = fobj G x) :
  (forall x y (f : hom C x y),
    hom_transport (ho x) (ho y) (fmap F f) = fmap G f) -> F = G.
Proof.
  destruct F as [fo fm fi fc], G as [go gm gi gc]; simpl in *.
  intro hm.
  assert (fo = go) as e by (apply functional_extensionality_dep; exact ho).
  destruct e.
  assert (fm = gm) as em.
  { apply functional_extensionality_dep; intro x.
    apply functional_extensionality_dep; intro y.
    apply functional_extensionality_dep; intro f.
    specialize (hm x y f). rewrite hom_transport_loop in hm. exact hm. }
  destruct em. f_equal; apply Prop_irrelevance.
Qed.

Definition reindexed_category (C : category) (A : Type) (i : A -> C) : category.
Proof.
  refine (@Build_category A (fun a b => hom C (i a) (i b))
    (fun a => identity (i a)) (fun a b c f g => compose f g) _ _ _).
  - intros a b f; apply compose_id_left.
  - intros a b f; apply compose_id_right.
  - intros a b c d f g h; apply compose_assoc.
Defined.

Arguments reindexed_category C {A} i.

Lemma reindexed_category_comp (C : category) (A B : Type)
    (i : A -> C) (j : B -> A) :
  reindexed_category (reindexed_category C i) j =
    reindexed_category C (fun x => i (j x)).
Proof. unfold reindexed_category; simpl; f_equal; apply Prop_irrelevance. Qed.

Definition reindex_inclusion (C : category) (A : Type) (i : A -> C) :
    functor (reindexed_category C i) C.
Proof.
  refine (@Build_functor (reindexed_category C i) C i (fun a b f => f) _ _);
    reflexivity.
Defined.

Arguments reindex_inclusion C {A} i.

Lemma reindexed_hom_transport (C : category) (A : Type) (i : A -> C)
    (x y x' y' : A) (hx : x = x') (hy : y = y')
    (f : hom (reindexed_category C i) x y) :
  @hom_transport (reindexed_category C i) x y x' y' hx hy f =
    @hom_transport C (i x) (i y) (i x') (i y')
      (f_equal i hx) (f_equal i hy) f.
Proof. destruct hx, hy; reflexivity. Qed.

Section Bijection.
Context (C : category) (A : Type) (i : A -> C) (j : C -> A).
Hypothesis ij : forall x, i (j x) = x.
Hypothesis ji : forall a, j (i a) = a.

Definition reindex_inverse : functor C (reindexed_category C i).
Proof.
  refine (@Build_functor C (reindexed_category C i) j
    (fun x y f => hom_transport (eq_sym (ij x)) (eq_sym (ij y)) f) _ _).
  - intro x; exact (@hom_transport_identity C x (i (j x)) (eq_sym (ij x))).
  - intros x y z f g; exact (@hom_transport_compose C x y z
      (i (j x)) (i (j y)) (i (j z))
      (eq_sym (ij x)) (eq_sym (ij y)) (eq_sym (ij z)) f g).
Defined.

Lemma reindex_forward_backward :
  functor_comp (reindex_inclusion C i) reindex_inverse =
    functor_id (reindexed_category C i).
Proof.
  apply (@functor_ext_pointwise (reindexed_category C i) (reindexed_category C i)
    (functor_comp (reindex_inclusion C i) reindex_inverse)
    (functor_id (reindexed_category C i)) ji).
  intros x y f; simpl.
  rewrite reindexed_hom_transport, hom_transport_twice.
  apply hom_transport_loop.
Qed.

Lemma reindex_backward_forward :
  functor_comp reindex_inverse (reindex_inclusion C i) = functor_id C.
Proof.
  apply (@functor_ext_pointwise C C
    (functor_comp reindex_inverse (reindex_inclusion C i)) (functor_id C) ij).
  intros x y f; simpl. rewrite hom_transport_twice. apply hom_transport_loop.
Qed.

Definition reindex_category_isomorphism :
    category_isomorphism (reindexed_category C i) C :=
  {| category_iso_forward := reindex_inclusion C i;
     category_iso_backward := reindex_inverse;
     category_iso_forward_backward := reindex_forward_backward;
     category_iso_backward_forward := reindex_backward_forward |}.
End Bijection.

Section Change.
Context (C : category) (A : Type) (i j : A -> C).
Hypothesis h : forall x, i x = j x.

Definition reindex_change : functor (reindexed_category C i) (reindexed_category C j).
Proof.
  refine (@Build_functor (reindexed_category C i) (reindexed_category C j)
    (fun x => x) (fun x y f => @hom_transport C _ _ _ _ (h x) (h y) f) _ _).
  - intro x; exact (@hom_transport_identity C (i x) (j x) (h x)).
  - intros x y z f g; exact (@hom_transport_compose C _ _ _ _ _ _ (h x) (h y) (h z) f g).
Defined.
End Change.

Definition reindex_equal_isomorphism (C : category) (A : Type) (i j : A -> C)
    (h : forall x, i x = j x) :
    category_isomorphism (reindexed_category C i) (reindexed_category C j).
Proof.
  refine {| category_iso_forward := reindex_change h;
            category_iso_backward := reindex_change (fun x => eq_sym (h x)) |}.
  - apply (@functor_ext_pointwise (reindexed_category C i) (reindexed_category C i)
      (functor_comp (reindex_change h) (reindex_change (fun x => eq_sym (h x))))
      (functor_id (reindexed_category C i)) (fun x => Logic.eq_refl x)).
    intros x y f; simpl. rewrite hom_transport_twice. apply hom_transport_loop.
  - apply (@functor_ext_pointwise (reindexed_category C j) (reindexed_category C j)
      (functor_comp (reindex_change (fun x => eq_sym (h x))) (reindex_change h))
      (functor_id (reindexed_category C j)) (fun x => Logic.eq_refl x)).
    intros x y f; simpl. rewrite hom_transport_twice. apply hom_transport_loop.
Defined.

Section Flatten.
Context (C : category) (A B : Type) (i : A -> C) (j : B -> A).
Definition reindex_flatten :
    functor (reindexed_category (reindexed_category C i) j)
      (reindexed_category C (fun x => i (j x))).
Proof.
  refine (@Build_functor _ _ (fun x => x) (fun x y f => f) _ _); reflexivity.
Defined.
Definition reindex_unflatten :
    functor (reindexed_category C (fun x => i (j x)))
      (reindexed_category (reindexed_category C i) j).
Proof.
  refine (@Build_functor _ _ (fun x => x) (fun x y f => f) _ _); reflexivity.
Defined.
Definition reindex_flat_isomorphism :
    category_isomorphism (reindexed_category (reindexed_category C i) j)
      (reindexed_category C (fun x => i (j x))).
Proof.
  refine {| category_iso_forward := reindex_flatten;
            category_iso_backward := reindex_unflatten |}.
  - apply (@functor_extensionality _ _ (functor_comp reindex_flatten reindex_unflatten)
      (functor_id _) eq_refl); reflexivity.
  - apply (@functor_extensionality _ _ (functor_comp reindex_unflatten reindex_flatten)
      (functor_id _) eq_refl); reflexivity.
Defined.
End Flatten.
