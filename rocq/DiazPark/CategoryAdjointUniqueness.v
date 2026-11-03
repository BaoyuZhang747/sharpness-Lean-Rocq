(** Actual uniqueness of a right adjoint, from the two units and counits. *)
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryAdjunction CategoryInjectives.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RightAdjoints.
Context {C D : category} {L : functor C D} {R S : functor D C}.
Variables (a : adjunction L R) (b : adjunction L S).
Definition right_adjoint_comparison_component (y : D) : hom C (fobj R y) (fobj S y) :=
  adjoint_to_right b (component (adj_counit a) y).

Lemma right_adjoint_comparison_formula {x : C} {y : D} (f : hom C x (fobj R y)) :
    adjoint_to_right b (adjoint_to_left a f) = compose f (right_adjoint_comparison_component y).
Proof. unfold adjoint_to_left, right_adjoint_comparison_component.
exact (adjoint_to_right_precompose b f (component (adj_counit a) y)). Qed.

Lemma right_adjoint_comparison_natural {x y : D} (f : hom D x y) :
    compose (fmap R f) (right_adjoint_comparison_component y) =
      compose (right_adjoint_comparison_component x) (fmap S f).
Proof.
unfold right_adjoint_comparison_component, adjoint_to_right.
rewrite <- compose_assoc.
pose proof (naturality (adj_unit b) (fmap R f)) as hu.
change (compose (fmap R f) (component (adj_unit b) (fobj R y)) =
  compose (component (adj_unit b) (fobj R x)) (fmap S (fmap L (fmap R f)))) in hu.
rewrite hu, compose_assoc.
transitivity (compose (component (adj_unit b) (fobj R x))
  (fmap S (compose (fmap L (fmap R f)) (component (adj_counit a) y)))).
- apply f_equal. symmetry; exact (fmap_compose S (fmap L (fmap R f)) (component (adj_counit a) y)).
-
pose proof (naturality (adj_counit a) f) as hc.
change (compose (fmap L (fmap R f)) (component (adj_counit a) y) =
  compose (component (adj_counit a) x) f) in hc.
rewrite hc.
transitivity (compose (component (adj_unit b) (fobj R x))
  (compose (fmap S (component (adj_counit a) x)) (fmap S f))).
+ apply f_equal. exact (fmap_compose S (component (adj_counit a) x) f).
+ symmetry; apply compose_assoc.
Qed.

Definition right_adjoint_comparison : nat_trans R S :=
  @Build_nat_trans D C R S right_adjoint_comparison_component
    (fun x y f => right_adjoint_comparison_natural f).
End RightAdjoints.

Lemma right_adjoint_comparison_inverse {C D : category} {L : functor C D}
    {R S : functor D C} (a : adjunction L R) (b : adjunction L S) y :
    compose (right_adjoint_comparison_component a b y)
      (right_adjoint_comparison_component b a y) = identity (fobj R y).
Proof.
rewrite <- (right_adjoint_comparison_formula b a).
unfold right_adjoint_comparison_component.
rewrite adjoint_left_right.
change (adjoint_to_right a (component (adj_counit a) y) = identity (fobj R y)).
unfold adjoint_to_right. exact (adj_triangle_right a y).
Qed.

Definition right_adjoint_unique_iso {C D : category} {L : functor C D}
    {R S : functor D C} (a : adjunction L R) (b : adjunction L S) :
    @isomorphism (functor_category D C) R S.
Proof.
refine (@Build_isomorphism (functor_category D C) R S
  (right_adjoint_comparison a b) (right_adjoint_comparison b a) _ _).
- apply nat_trans_ext; intro y; exact (right_adjoint_comparison_inverse a b y).
- apply nat_trans_ext; intro y; exact (right_adjoint_comparison_inverse b a y).
Defined.




Definition isomorphism_composition {C : category} {x y z : C}
    (e : isomorphism x y) (f : isomorphism y z) : isomorphism x z.
Proof.
refine (@Build_isomorphism C x z (compose (iso_hom e) (iso_hom f))
  (compose (iso_inv f) (iso_inv e)) _ _).
- rewrite compose_assoc, <- (compose_assoc (iso_hom f)), iso_hom_inv,
    compose_id_left. exact (iso_hom_inv e).
- rewrite compose_assoc, <- (compose_assoc (iso_inv e)), iso_inv_hom,
    compose_id_left. exact (iso_inv_hom f).
Defined.
