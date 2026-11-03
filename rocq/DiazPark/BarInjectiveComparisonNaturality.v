From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalCohomology HomologicalCohomologyMaps HomologicalConnecting HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison CategoryResolutionLimitMaps
  BarComplex BarNaturality BarInjectiveResolutionTail BarInjectiveTailMaps
  BarInjectiveComparison BarInjectiveDegreeOneNaturality BarResolutionConnectingNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalConnecting
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarInjectiveResolutionTail DiazParkBarInjectiveTailMaps
  DiazParkBarInjectiveComparison DiazParkBarInjectiveDegreeOneNaturality
  DiazParkBarResolutionConnectingNaturality.

Module DiazParkBarInjectiveComparisonNaturality.
Section Naturality.
Variable R : pzRingType.
Variable C : category.
Local Opaque module_quotient linear_preimage linear_kernel linear_image.

Lemma bar_shift_inverse_naturality (D E : module_codiagram R C)
    (J : injective_resolution D) (J' : injective_resolution E) (u : nat_trans D E)
    (m : injective_resolution_map J J' u) n (q : cohomology (bar_complex D) n.+2) :
  module_hom_fun (iso_inv (bar_resolution_dimension_shift J' n))
    (cohomology_map (bar_cochain_map u) n.+2 q) =
  cohomology_map (bar_cochain_map (syzygy_comparison m)) n.+1
    (module_hom_fun (iso_inv (bar_resolution_dimension_shift J n)) q).
Proof.
apply (@module_iso_hom_injective R _ _ (bar_resolution_dimension_shift J' n)).
rewrite module_iso_inv_hom_apply.
change (cohomology_map (bar_cochain_map u) n.+2 q =
  connecting_map (injective_syzygy_bar_short_exact J') n.+1
    (cohomology_map (bar_cochain_map (syzygy_comparison m)) n.+1
      (module_hom_fun (iso_inv (bar_resolution_dimension_shift J n)) q))).
rewrite resolution_connecting_naturality.
congr (cohomology_map (bar_cochain_map u) n.+2 _).
symmetry; exact: (module_iso_inv_hom_apply (bar_resolution_dimension_shift J n) q).
Qed.

Lemma tail_cohomology_iso_apply (D : module_codiagram R C) (J : injective_resolution D)
    n (q : cohomology (limit_complex (injective_tail_complex J)) n.+1) :
  module_hom_fun (iso_hom (injective_tail_cohomology_iso J n)) q = q.
Proof. reflexivity. Qed.

Lemma tail_cohomology_map_apply (D E : module_codiagram R C)
    (J : injective_resolution D) (J' : injective_resolution E) (u : nat_trans D E)
    (m : injective_resolution_map J J' u) n
    (q : cohomology (limit_complex (injective_tail_complex J)) n.+1) :
  cohomology_map (limit_cochain_map (resolution_map_complex m)) n.+2 q =
  cohomology_map (limit_cochain_map (injective_tail_complex_map m)) n.+1 q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Theorem bar_injective_positive_naturality n : forall (D E : module_codiagram R C)
    (J : injective_resolution D) (J' : injective_resolution E) (u : nat_trans D E)
    (m : injective_resolution_map J J' u) (q : cohomology (bar_complex D) n.+1),
  cohomology_map (limit_cochain_map (resolution_map_complex m)) n.+1
    (module_hom_fun (iso_hom (bar_injective_positive_iso n J)) q) =
  module_hom_fun (iso_hom (bar_injective_positive_iso n J'))
    (cohomology_map (bar_cochain_map u) n.+1 q).
Proof.
elim: n => [|n ih] D E J J' u m q.
- exact: bar_degree_one_naturality.
- change (cohomology_map (limit_cochain_map (resolution_map_complex m)) n.+2
    (module_hom_fun (iso_hom (injective_tail_cohomology_iso J n))
      (module_hom_fun (iso_hom (bar_injective_positive_iso n (injective_tail_resolution J)))
        (module_hom_fun (iso_inv (bar_resolution_dimension_shift J n)) q))) =
    module_hom_fun (iso_hom (injective_tail_cohomology_iso J' n))
      (module_hom_fun (iso_hom (bar_injective_positive_iso n (injective_tail_resolution J')))
        (module_hom_fun (iso_inv (bar_resolution_dimension_shift J' n))
          (cohomology_map (bar_cochain_map u) n.+2 q)))).
  rewrite !tail_cohomology_iso_apply (@bar_shift_inverse_naturality D E J J' u m n q).
  rewrite (tail_cohomology_map_apply m).
  exact: (@ih (injective_syzygy J) (injective_syzygy J') (injective_tail_resolution J) (injective_tail_resolution J')
    (syzygy_comparison m) (injective_tail_resolution_map m)
    (module_hom_fun (iso_inv (bar_resolution_dimension_shift J n)) q)).
Qed.

End Naturality.
End DiazParkBarInjectiveComparisonNaturality.


