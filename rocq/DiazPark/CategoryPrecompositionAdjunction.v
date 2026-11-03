(** An adjunction L left adjoint to U induces restriction along U left
    adjoint to restriction along L, with explicit unit and counit. *)
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RestrictionAdjunction.
Variables C D E : category.
Variables (L : functor C D) (U : functor D C).
Variable a : adjunction L U.

Definition restriction_unit_component (F : functor C E) :
    nat_trans F (functor_comp L (functor_comp U F)).
Proof.
refine (@Build_nat_trans C E F (functor_comp L (functor_comp U F))
  (fun x => fmap F (component (adj_unit a) x)) _).
intros x y f.
change (compose (fmap F f) (fmap F (component (adj_unit a) y)) =
  compose (fmap F (component (adj_unit a) x)) (fmap F (fmap U (fmap L f)))).
rewrite <- !fmap_compose. apply f_equal. exact (naturality (adj_unit a) f).
Defined.

Definition restriction_counit_component (F : functor D E) :
    nat_trans (functor_comp U (functor_comp L F)) F.
Proof.
refine (@Build_nat_trans D E (functor_comp U (functor_comp L F)) F
  (fun x => fmap F (component (adj_counit a) x)) _).
intros x y f.
change (compose (fmap F (fmap L (fmap U f))) (fmap F (component (adj_counit a) y)) =
  compose (fmap F (component (adj_counit a) x)) (fmap F f)).
rewrite <- !fmap_compose. apply f_equal. exact (naturality (adj_counit a) f).
Defined.

Definition precomposition_adjunction :
    adjunction (precomposition E U) (precomposition E L).
Proof.
unshelve refine (@Build_adjunction (functor_category C E) (functor_category D E)
  (precomposition E U) (precomposition E L)
  (@Build_nat_trans (functor_category C E) (functor_category C E)
    (functor_id _) (functor_comp (precomposition E U) (precomposition E L))
    restriction_unit_component _)
  (@Build_nat_trans (functor_category D E) (functor_category D E)
    (functor_comp (precomposition E L) (precomposition E U)) (functor_id _)
    restriction_counit_component _) _ _).
- intros F G t. apply nat_trans_ext; intro x.
  symmetry. exact (naturality t (component (adj_unit a) x)).
- intros F G t. apply nat_trans_ext; intro x.
  symmetry. exact (naturality t (component (adj_counit a) x)).
- intro F. apply nat_trans_ext; intro y.
  change (compose (fmap F (component (adj_unit a) (fobj U y)))
    (fmap F (fmap U (component (adj_counit a) y))) = identity (fobj F (fobj U y))).
  transitivity (fmap F (compose (component (adj_unit a) (fobj U y)) (fmap U (component (adj_counit a) y)))).
  + symmetry; apply fmap_compose.
  + rewrite (adj_triangle_right a y). apply fmap_id.
- intro F. apply nat_trans_ext; intro x.
  change (compose (fmap F (fmap L (component (adj_unit a) x)))
    (fmap F (component (adj_counit a) (fobj L x))) = identity (fobj F (fobj L x))).
  transitivity (fmap F (compose (fmap L (component (adj_unit a) x)) (component (adj_counit a) (fobj L x)))).
  + symmetry; apply fmap_compose.
  + rewrite (adj_triangle_left a x). apply fmap_id.
Defined.
End RestrictionAdjunction.

Arguments precomposition_adjunction {C D} E {L U} a.


