(** The actual right Kan product formula and coordinates of its adjunction
    unit, from a proved discrete initial family in the structured comma. *)
From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryExtensionality CategoryLimits
  CategoryAdjunction CategoryComma CategoryStructured CategoryModules
  CategoryModuleProducts CategoryModuleLimits CategoryInitialFamily
  CategoryModuleInitialFamily CategoryModuleRightKan CategoryNaturalIso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RanProduct.
Variable R : pzRingType.
Variables C D : category.
Variable L : functor C D.
Variable d : D.
Variable T : initial_family (structured_category L d).

Definition module_ran_product_iso (M : module_diagram R C) :
    @isomorphism (module_category R) (fobj (fobj (module_ran R L) M) d)
      (initial_family_product T (functor_comp (structured_projection L d) M)) :=
  module_initial_family_iso T (functor_comp (structured_projection L d) M).

Definition module_ran_product_nat_iso :
    @isomorphism
      (functor_category (functor_category C (module_category R)) (module_category R))
      (functor_comp (module_ran R L) (evaluation_functor D (module_category R) d))
      (functor_comp (precomposition (module_category R) (structured_projection L d))
        (initial_family_product_functor R T)).
Proof.
  refine (@nat_iso_of_components (functor_category C (module_category R))
    (module_category R)
    (functor_comp (module_ran R L) (evaluation_functor D (module_category R) d))
    (functor_comp (precomposition (module_category R) (structured_projection L d))
      (initial_family_product_functor R T)) module_ran_product_iso _).
  intros M N t.
  exact (naturality (iso_hom (module_initial_family_nat_iso R T))
    (nat_whisker_left (structured_projection L d) t)).
Defined.

Lemma module_ran_product_coordinate (M : module_diagram R C)
    (i : initial_family_index T) :
    @compose (module_category R) _ _ _ (iso_hom (module_ran_product_iso M))
      (module_product_projection _ i) =
      module_limit_projection (functor_comp (structured_projection L d) M)
        (initial_family_object T i).
Proof.
  exact (@module_initial_family_iso_coordinate R (structured_category L d)
    T (functor_comp (structured_projection L d) M) i).
Qed.

Lemma module_ran_product_unit_coordinate (H : module_diagram R D)
    (i : initial_family_index T) :
    @compose (module_category R) _ _ _
      (compose
        (component (component (adj_unit (module_ran_adjunction R L)) H) d)
        (iso_hom (module_ran_product_iso (functor_comp L H))))
      (module_product_projection _ i) =
      fmap H (structured_arrow (initial_family_object T i)).
Proof.
  rewrite compose_assoc.
  transitivity (compose
    (component (component (adj_unit (module_ran_adjunction R L)) H) d)
    (module_limit_projection
      (functor_comp (structured_projection L d) (functor_comp L H))
      (initial_family_object T i))).
  - apply f_equal. exact (@module_ran_product_coordinate (functor_comp L H) i).
  - exact (@module_ran_unit_coordinate R C D L H d (initial_family_object T i)).
Qed.
End RanProduct.

Arguments module_ran_product_iso R {C D} L {d} T M.
Arguments module_ran_product_nat_iso R {C D} L {d} T.
