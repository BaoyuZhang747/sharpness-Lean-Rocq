(** Native all-degree, coefficient-natural comparison along the actual q functor. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryDerivedLimits FusionSystems FusionOrbit FusionSaturation
  ModuleInfrastructure BarComplex BarDerivedComparison HomologicalCohomologyMaps.
From DiazParkV16b Require Import NormalizerOrbitPairCategory NormalizerOrbitForgetCofinality
  CategoryBarPullback CategoryInducedBarNaturalComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkBarComplex DiazParkBarDerivedComparison DiazParkCohomologyMaps DPCategoryBarPullbackMaps.
Local Open Scope group_scope.

Module DPNormalizerOrbitForgetHigherLimits.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : comPzRingType.
Local Notation C := (DPNormalizerOrbitPair.pair_category F).
Local Notation D := (DPFusionOrbit.centric_orbit_category F).
Local Notation q := (DPNormalizerOrbitPair.forget F).
Let h := DPNormalizerOrbitForgetCofinality.forget_comma_augmented_exact pS sat R.

Definition forget_higher_limit_iso (M : module_codiagram R D) n :
  @isomorphism (module_category R) (derived_limit R M n)
    (derived_limit R (functor_comp (functor_op q) M) n) :=
  comma_exact_higher_limit_iso R q h M n.

Definition forget_higher_limit_nat_iso n : @isomorphism
  (functor_category (functor_category (opposite D) (module_category R)) (module_category R))
  (derived_limit_functor R (opposite D) n)
  (functor_comp (precomposition (module_category R) (functor_op q))
    (derived_limit_functor R (opposite C) n)) :=
  comma_exact_higher_limit_nat_iso R q h n.

Theorem forget_higher_limit_iso_hom (M : module_codiagram R D) n (z : derived_limit R M n) :
  module_hom_fun (iso_hom (forget_higher_limit_iso M n)) z =
  module_hom_fun (iso_hom (bar_derived_limit_iso (functor_comp (functor_op q) M) n))
    (cohomology_map (bar_pullback_cochain_map q M) n
      (module_hom_fun (iso_inv (bar_derived_limit_iso M n)) z)).
Proof. exact: comma_exact_higher_limit_iso_hom. Qed.
End Comparison.
End DPNormalizerOrbitForgetHigherLimits.
