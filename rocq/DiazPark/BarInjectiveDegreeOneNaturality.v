From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness CategoryModuleLimits
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  HomologicalDiagramInjectives HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison CategoryResolutionLimitMaps
  BarComplex BarNaturality BarInjectiveResolutionTail BarInjectiveTailMaps BarConnectingLimit
  BarInjectiveDegreeOne BarResolutionConnectingNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarInjectiveResolutionTail
  DiazParkBarInjectiveTailMaps DiazParkBarConnectingLimit DiazParkBarInjectiveDegreeOne
  DiazParkBarResolutionConnectingNaturality.

Module DiazParkBarInjectiveDegreeOneNaturality.
Section Naturality.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_codiagram R C.
Variables (J : injective_resolution D) (J' : injective_resolution E).
Variable u : nat_trans D E.
Variable m : injective_resolution_map J J' u.
Let a := resolution_map_complex m.
Let L := limit_complex (injective_resolution_complex J).
Let L' := limit_complex (injective_resolution_complex J').

Lemma first_cycle_limit_naturality (z : cycle_module L 1) :
  first_cycle_limit J' (cycle_map (limit_cochain_map a) 1 z) =
    limit_action (syzygy_comparison m) (first_cycle_limit J z).
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep => x.
apply submodule_val_injective; rewrite first_cycle_limit_coordinate limit_action_coordinate
  syzygy_comparison_val first_cycle_limit_coordinate.
change (module_limit_val (limit_action (diagram_cochain_map_at a 1) (cycle_inclusion L 1 z)) x =
  module_hom_fun (component (diagram_cochain_map_at a 1) x) (module_limit_val (cycle_inclusion L 1 z) x)).
exact: limit_action_coordinate.
Qed.

Lemma first_cycle_connecting_naturality (z : cycle_module L 1) :
  first_cycle_connecting J' (cycle_map (limit_cochain_map a) 1 z) =
    cohomology_map (bar_cochain_map u) 1 (first_cycle_connecting J z).
Proof.
change (limit_connecting (injective_syzygy_bar_short_exact J')
  (first_cycle_limit J' (cycle_map (limit_cochain_map a) 1 z)) =
    cohomology_map (bar_cochain_map u) 1 (first_cycle_connecting J z)).
rewrite first_cycle_limit_naturality.
exact: resolution_limit_connecting_naturality.
Qed.

End Naturality.

Section IsoNaturality.
Variable R : pzRingType.
Variable C : category.
Local Opaque module_quotient linear_preimage linear_kernel linear_image.

Lemma bar_degree_one_inverse_pi (D : module_codiagram R C) (J : injective_resolution D)
    (z : cycle_module (limit_complex (injective_resolution_complex J)) 1) :
  module_hom_fun (iso_inv (bar_injective_degree_one_iso J))
    (quotient_pi (boundaries_in_cycles (limit_complex (injective_resolution_complex J)) 1) z) =
  first_cycle_connecting J z.
Proof. exact: quotient_iso_map_pi. Qed.

Variables D E : module_codiagram R C.
Variables (J : injective_resolution D) (J' : injective_resolution E).
Variable u : nat_trans D E.
Variable m : injective_resolution_map J J' u.
Let a := resolution_map_complex m.

Lemma bar_degree_one_inverse_naturality
    (q : cohomology (limit_complex (injective_resolution_complex J)) 1) :
  module_hom_fun (iso_inv (bar_injective_degree_one_iso J'))
    (cohomology_map (limit_cochain_map a) 1 q) =
  cohomology_map (bar_cochain_map u) 1
    (module_hom_fun (iso_inv (bar_injective_degree_one_iso J)) q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi !bar_degree_one_inverse_pi.
exact: first_cycle_connecting_naturality.
Qed.

Theorem bar_degree_one_naturality (q : cohomology (bar_complex D) 1) :
  cohomology_map (limit_cochain_map a) 1
    (module_hom_fun (iso_hom (bar_injective_degree_one_iso J)) q) =
  module_hom_fun (iso_hom (bar_injective_degree_one_iso J'))
    (cohomology_map (bar_cochain_map u) 1 q).
Proof.
apply (@module_iso_hom_injective R _ _ (iso_symm (bar_injective_degree_one_iso J'))).
change (module_hom_fun (iso_inv (bar_injective_degree_one_iso J'))
  (cohomology_map (limit_cochain_map a) 1
    (module_hom_fun (iso_hom (bar_injective_degree_one_iso J)) q)) =
  module_hom_fun (iso_inv (bar_injective_degree_one_iso J'))
    (module_hom_fun (iso_hom (bar_injective_degree_one_iso J'))
      (cohomology_map (bar_cochain_map u) 1 q))).
by rewrite bar_degree_one_inverse_naturality !module_iso_hom_inv_apply.
Qed.

End IsoNaturality.
End DiazParkBarInjectiveDegreeOneNaturality.
