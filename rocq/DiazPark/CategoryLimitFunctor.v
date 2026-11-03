(** Bundled ordinary limit functors and their actual natural comparisons.
    The chosen universal cones are explicit arguments. Module completeness
    supplies them concretely in CategoryModuleLimitFunctor. *)

From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryLimits CategoryAdjunction CategoryLimitMaps.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition chosen_limit_functor {C D : category}
    (K : forall F : functor C D, limiting_cone F) :
    functor (functor_category C D) D.
Proof.
  refine (@Build_functor (functor_category C D) D
    (fun F => limit_object (K F))
    (fun F G a => limit_map (K F) (K G) a) _ _).
  - intro F. apply limit_map_id.
  - intros F G H a b. symmetry. apply limit_map_comp.
Defined.

Definition left_adjoint_limit_nat_iso {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (KD : forall F : functor D E, limiting_cone F)
    (KC : forall F : functor C E, limiting_cone F) :
    @isomorphism (functor_category (functor_category D E) E)
      (chosen_limit_functor KD)
      (functor_comp (precomposition E L) (chosen_limit_functor KC)).
Proof.
  refine (@nat_iso_of_components (functor_category D E) E
    (chosen_limit_functor KD)
    (functor_comp (precomposition E L) (chosen_limit_functor KC))
    (fun F => left_adjoint_limit_iso a F (KD F) (KC (functor_comp L F))) _).
  intros F G t.
  exact (@left_adjoint_limit_iso_natural C D E L R a F G (KD F) (KD G)
    (KC (functor_comp L F)) (KC (functor_comp L G)) t).
Defined.

Lemma limit_to_initial_hom {C D : category} {F : functor C D}
    (K : limiting_cone F) (i : initial_object C) :
    iso_hom (limit_unique_iso K (initial_limit F i)) =
      cone_leg (limit_cone K) (initial_point i).
Proof. apply compose_id_right. Qed.

Definition chosen_limit_initial_nat_iso {C D : category}
    (K : forall F : functor C D, limiting_cone F) (i : initial_object C) :
    @isomorphism (functor_category (functor_category C D) D)
      (chosen_limit_functor K) (evaluation_functor C D (initial_point i)).
Proof.
  refine (@nat_iso_of_components (functor_category C D) D
    (chosen_limit_functor K) (evaluation_functor C D (initial_point i))
    (fun F => limit_unique_iso (K F) (initial_limit F i)) _).
  intros F G a.
  change (compose (limit_map (K F) (K G) a)
    (iso_hom (limit_unique_iso (K G) (initial_limit G i))) =
    compose (iso_hom (limit_unique_iso (K F) (initial_limit F i)))
      (component a (initial_point i))).
  rewrite !limit_to_initial_hom. apply limit_map_fac.
Defined.
