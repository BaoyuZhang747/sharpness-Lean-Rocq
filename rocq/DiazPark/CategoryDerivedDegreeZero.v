(** Degree zero of the actual derived-limit functor is the actual compatible
    family limit, naturally in coefficients. No bar computation is needed. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor CategoryModuleExactness
  CategoryEnoughInjectives CategoryInjectiveResolutionComparison CategoryDerivedLimits
  BarInjectiveDegreeZero BarInjectiveDegreeZeroNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarInjectiveDegreeZero DiazParkBarInjectiveDegreeZeroNaturality.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution injective_resolution_comparison.

Definition derived_degree_zero_iso (R : pzRingType) {C : category} (F : module_diagram R C) :
    @isomorphism (module_category R) (derived_limit R F 0%N) (module_limit_type F) :=
  iso_symm (injective_degree_zero_iso (chosen_injective_resolution R F)).
Arguments derived_degree_zero_iso R {C} F.

Definition derived_degree_zero_nat_iso (R : pzRingType) (C : category) :
    @isomorphism
      (functor_category (functor_category C (module_category R)) (module_category R))
      (derived_limit_functor R C 0%N) (module_limit_functor R C).
Proof.
apply iso_symm.
refine (@nat_iso_of_components (functor_category C (module_category R)) (module_category R)
  (module_limit_functor R C) (derived_limit_functor R C 0%N)
  (fun F => injective_degree_zero_iso (chosen_injective_resolution R F)) _).
intros F G u; apply module_hom_ext; intro v; symmetry.
exact (injective_degree_zero_naturality
  (injective_resolution_comparison (chosen_injective_resolution R F)
    (chosen_injective_resolution R G) u) v).
Defined.

Theorem derived_degree_zero_zero (R : pzRingType) {C : category} (F : module_diagram R C)
    (h : forall v : module_limit_type F, v = 0) (q : derived_limit R F 0%N) : q = 0.
Proof.
apply (@module_iso_hom_injective R _ _ (derived_degree_zero_iso R F)).
rewrite module_hom_zero. exact: h.
Qed.
