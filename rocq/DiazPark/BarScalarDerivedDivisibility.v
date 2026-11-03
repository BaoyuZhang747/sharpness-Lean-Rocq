From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryDerivedLimits CategoryEnoughInjectives CategoryInjectiveResolutionComparison
  MackeyStructures MackeySubquotients MackeyBarReduction HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  BarComplex BarNaturality BarDerivedComparison BarHigherLimitVanishing
  BarScalarDivisibility BarScalarHigherLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkBarComplex DiazParkBarNaturality
  DiazParkBarDerivedComparison DiazParkBarHigherLimitVanishing DiazParkScalarHigherLimits.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution injective_resolution_comparison.

Section DerivedDivisibility.
Variable R : comPzRingType.
Variables C D : category.
Variable B : mackey_shape C.
Variable L : functor D C.
Variable M : mackey_module R B.
Variable r : R.
Let K := subfunctor_mackey (mackey_scalar_kernel M r).
Let I := subfunctor_mackey (mackey_scalar_image M r).
Let Q := quotient_mackey (mackey_scalar_image M r).

Definition scalar_image_higher_limit_iso
    (hK : mackey_bar_acyclic L K) n :
  @isomorphism (module_category R)
    (derived_limit R (mackey_codiagram L M) n.+1)
    (derived_limit R (mackey_codiagram L I) n.+1) :=
  module_iso_comp (iso_symm (bar_derived_limit_iso (mackey_codiagram L M) n.+1))
    (module_iso_comp (@scalar_image_cohomology_iso R C D B L M r hK n)
      (bar_derived_limit_iso (mackey_codiagram L I) n.+1)).

Lemma scalar_image_higher_limit_iso_hom
    (hK : mackey_bar_acyclic L K) n q :
  module_hom_fun (iso_hom (scalar_image_higher_limit_iso hK n)) q =
  module_hom_fun (derived_limit_map R
    (mackey_codiagram_map L (mackey_scalar_to_image M r)) n.+1) q.
Proof.
change (module_hom_fun (iso_hom (bar_derived_limit_iso (mackey_codiagram L I) n.+1))
  (cohomology_map (bar_cochain_map (mackey_codiagram_map L (mackey_scalar_to_image M r))) n.+1
    (module_hom_fun (iso_inv (bar_derived_limit_iso (mackey_codiagram L M) n.+1)) q)) =
  module_hom_fun (derived_limit_map R
    (mackey_codiagram_map L (mackey_scalar_to_image M r)) n.+1) q).
by rewrite -bar_derived_naturality module_iso_inv_hom_apply.
Qed.

Theorem mackey_scalar_higher_limit_surjective
    (hK : mackey_bar_acyclic L K) (hQ : mackey_bar_acyclic L Q) n :
  forall q : derived_limit R (mackey_codiagram L M) n.+1,
    exists y, r *: y = q.
Proof.
move=> q.
pose e := bar_derived_limit_iso (mackey_codiagram L M) n.+1.
have [y hy] := @mackey_scalar_cohomology_surjective R C D B L M r hK hQ n
  (module_hom_fun (iso_inv e) q).
exists (module_hom_fun (iso_hom e) y).
by rewrite -module_hom_scale hy module_iso_inv_hom_apply.
Qed.

Theorem mackey_scalar_higher_limit_surjective_of_derived
    (hK : forall n (q : derived_limit R (mackey_codiagram L K) n.+1), q = 0)
    (hQ : forall n (q : derived_limit R (mackey_codiagram L Q) n.+1), q = 0) n :
  forall q : derived_limit R (mackey_codiagram L M) n.+1,
    exists y, r *: y = q.
Proof.
apply: mackey_scalar_higher_limit_surjective.
- apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram L K)); exact: hK.
- apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram L Q)); exact: hQ.
Qed.

End DerivedDivisibility.
