From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryModules
  CategoryModuleLimits ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalCohomology HomologicalCohomologyMaps HomologicalDegreeZero HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison CategoryResolutionLimitMaps
  CategoryEnoughInjectives CategoryDerivedLimits BarComplex BarNaturality BarDegreeZero
  BarInjectiveDegreeZero BarInjectiveDegreeZeroNaturality BarInjectiveComparisonAll
  BarInjectiveComparisonNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalDegreeZero
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarDegreeZero
  DiazParkBarInjectiveDegreeZero DiazParkBarInjectiveDegreeZeroNaturality
  DiazParkBarInjectiveComparisonAll DiazParkBarInjectiveComparisonNaturality.

Module DiazParkBarDerivedComparison.
Section Comparison.
Variable R : pzRingType.
Variable C : category.
Local Opaque module_quotient linear_preimage linear_kernel linear_image.

Lemma bar_zero_limit_naturality (D E : module_codiagram R C) (u : nat_trans D E)
    (q : cohomology (bar_complex D) 0) :
  limit_action u (module_hom_fun (iso_hom (bar_zero_cohomology_limit_iso D)) q) =
  module_hom_fun (iso_hom (bar_zero_cohomology_limit_iso E))
    (cohomology_map (bar_cochain_map u) 0 q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi.
change (limit_action u (bar_cycle_to_limit D (cohomology_zero_cycle (bar_complex D)
    (quotient_pi (boundaries_in_cycles (bar_complex D) 0) z))) =
  bar_cycle_to_limit E (cohomology_zero_cycle (bar_complex E)
    (quotient_pi (boundaries_in_cycles (bar_complex E) 0) (cycle_map (bar_cochain_map u) 0 z)))).
rewrite !cohomology_zero_cycle_pi.
apply module_limit_val_injective; apply functional_extensionality_dep => x.
rewrite limit_action_coordinate; reflexivity.
Qed.

Theorem bar_injective_cohomology_naturality (D E : module_codiagram R C)
    (J : injective_resolution D) (J' : injective_resolution E) (u : nat_trans D E)
    (m : injective_resolution_map J J' u) n (q : cohomology (bar_complex D) n) :
  cohomology_map (limit_cochain_map (resolution_map_complex m)) n
    (module_hom_fun (iso_hom (bar_injective_cohomology_iso J n)) q) =
  module_hom_fun (iso_hom (bar_injective_cohomology_iso J' n))
    (cohomology_map (bar_cochain_map u) n q).
Proof.
case: n q => [|n] q.
- change (cohomology_map (limit_cochain_map (resolution_map_complex m)) 0
    (module_hom_fun (iso_hom (injective_degree_zero_iso J))
      (module_hom_fun (iso_hom (bar_zero_cohomology_limit_iso D)) q)) =
    module_hom_fun (iso_hom (injective_degree_zero_iso J'))
      (module_hom_fun (iso_hom (bar_zero_cohomology_limit_iso E))
        (cohomology_map (bar_cochain_map u) 0 q))).
  by rewrite (injective_degree_zero_naturality m) bar_zero_limit_naturality.
- exact: bar_injective_positive_naturality.
Qed.

Definition bar_cohomology_functor (n : nat) :
    functor (functor_category (opposite C) (module_category R)) (module_category R).
Proof.
refine (@Build_functor (functor_category (opposite C) (module_category R)) (module_category R)
  (fun D => [the lmodType R of cohomology (bar_complex D) n])
  (fun D E u => module_hom_of_linear (cohomology_map (bar_cochain_map u) n)) _ _).
- move=> D; apply module_hom_ext => q.
  change (cohomology_map (bar_cochain_map (nat_id D)) n q = q).
  have [z <-] := quotient_pi_surjective q.
  rewrite cohomology_map_pi; congr (quotient_pi _ _).
  apply submodule_val_injective; reflexivity.
- move=> D E F u v; apply module_hom_ext => q.
  change (cohomology_map (bar_cochain_map (nat_comp u v)) n q =
    cohomology_map (bar_cochain_map v) n (cohomology_map (bar_cochain_map u) n q)).
  have [z <-] := quotient_pi_surjective q.
  rewrite !cohomology_map_pi; congr (quotient_pi _ _).
  apply submodule_val_injective; reflexivity.
Defined.

Local Opaque chosen_injective_resolution injective_resolution_comparison.

Definition bar_derived_limit_iso (D : module_codiagram R C) n :
    @isomorphism (module_category R) [the lmodType R of cohomology (bar_complex D) n]
      (derived_limit R D n) := bar_chosen_injective_cohomology_iso D n.

(** The actual natural isomorphism to the independently constructed right-
    derived limit functor. It includes degree zero and arbitrary coefficients. *)
Definition bar_derived_limit_natural_iso n :
    @isomorphism (functor_category
      (functor_category (opposite C) (module_category R)) (module_category R))
      (bar_cohomology_functor n) (derived_limit_functor R (opposite C) n).
Proof.
apply: (@nat_iso_of_components _ _ (bar_cohomology_functor n)
  (derived_limit_functor R (opposite C) n) (fun D => bar_derived_limit_iso D n)).
move=> D E u; apply module_hom_ext => q; symmetry.
exact: (bar_injective_cohomology_naturality
  (injective_resolution_comparison (chosen_injective_resolution R D)
    (chosen_injective_resolution R E) u) q).
Defined.

End Comparison.
End DiazParkBarDerivedComparison.
