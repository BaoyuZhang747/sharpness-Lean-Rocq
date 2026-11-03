From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalCohomology
  HomologicalConnectingIso HomologicalModuleIso HomologicalDiagramInjectives HomologicalDiagramLimits
  CategoryInjectiveResolution BarComplex BarResolutionInjective
  BarInjectiveResolutionTail BarInjectiveDegreeOne.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalConnectingIso
  DiazParkHomologicalModuleIso DiazParkBarComplex DiazParkBarResolutionInjective
  DiazParkBarInjectiveResolutionTail DiazParkBarInjectiveDegreeOne.

Module DiazParkBarInjectiveComparison.
Section Comparison.
Variable R : pzRingType.
Variable C : category.

Local Opaque module_quotient linear_preimage linear_kernel linear_image.

Definition bar_resolution_dimension_shift (D : module_codiagram R C)
    (J : injective_resolution D) n : @isomorphism (module_category R)
    [the lmodType R of cohomology (bar_complex (injective_syzygy J)) n.+1]
    [the lmodType R of cohomology (bar_complex D) n.+2] :=
  positive_connecting_iso (injective_syzygy_bar_short_exact J)
    (injective_bar_positive_acyclic (injective_resolution_term_injective J 0)) n.

(** The comparison is assembled from the actual degree-one quotient map and
    the proved connecting isomorphisms. The displayed injective resolution
    is ordinary mathematical data, and can be instantiated by the separately
    constructed chosen injective resolution. No comparison premise occurs. *)
Fixpoint bar_injective_positive_iso n : forall (D : module_codiagram R C)
    (J : injective_resolution D), @isomorphism (module_category R)
      [the lmodType R of cohomology (bar_complex D) n.+1]
      [the lmodType R of cohomology (limit_complex (injective_resolution_complex J)) n.+1].
Proof.
case: n => [|n] D J.
- exact: bar_injective_degree_one_iso.
- refine (module_iso_comp (iso_symm (bar_resolution_dimension_shift J n)) _).
  refine (module_iso_comp (@bar_injective_positive_iso n (injective_syzygy J)
    (injective_tail_resolution J)) _).
  exact: injective_tail_cohomology_iso.
Defined.

End Comparison.
End DiazParkBarInjectiveComparison.
