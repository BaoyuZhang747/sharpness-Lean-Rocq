(** Every component of the canonical spectral edge is the actual replacement
    projection; the spectral and elementary constructions agree literally. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleLimits
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalDiagramInjectives
  HomologicalCohomology HomologicalCohomologyMaps HomologicalDegreeZero HomologicalModuleIso BarComplex BarDegreeZero CategoryComplexIso.
From DiazParkV16b Require Import CochainZeroCycleNaturality FirstQuadrantCochainEdge FirstQuadrantCochainEdgeComparison
  FirstQuadrantCochainSpectralSecond FirstQuadrantFilteredPages FirstQuadrantFilteredSecondIso
  FirstQuadrantFilteredEdgeComparison CategoryCochainReplacement CategoryCochainReplacementTotal
  CategoryCochainCohomologyDiagram CategoryCochainReplacementVertical CategoryCochainReplacementAcyclic
  CategoryCochainReplacementEdge CategoryCochainReplacementSpectralSecond CategoryCochainReplacementSpectralSecondEdges
  CategoryCochainFilteredSecond CategoryCochainFilteredCollapse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalDegreeZero
  DiazParkHomologicalModuleIso DiazParkBarComplex DiazParkBarDegreeZero DPCochainZeroCycleNaturality
  DPFirstQuadrantEdge DPFirstQuadrantEdgeComparison DPColumnSecondPage DPFirstQuadrantFilteredPages
  DPFirstQuadrantFilteredSecondIso DPFirstQuadrantFilteredEdgeComparison.

Section Edge.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).

Lemma replacement_filtered_second_limit_edge n (x : replacement_filtered_page K 1 0 n) :
    module_hom_fun (iso_hom (replacement_filtered_second_zero_limit_iso K n)) x =
      module_hom_fun (iso_hom (replacement_edge_limit_iso K n)) (filtered_second_to_edge x).
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep; intro c.
change (submodule_val (cohomology_zero_cycle (bar_complex (cochain_cohomology_diagram K n))
  (cohomology_map (replacement_cohomology_row_map K n) 0
    (module_hom_fun (iso_hom (second_page_horizontal_iso (cochain_replacement_bicomplex K) 0 n))
      (module_hom_fun (iso_hom (filtered_second_native_iso (cochain_replacement_bicomplex K) 0 n)) x)))) c tt =
  (module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K 0 n))
    (submodule_val (filtered_second_to_edge x))) c tt).
rewrite cohomology_zero_cycle_map_val; reflexivity.
Qed.

Theorem replacement_filtered_total_limit_iso_eq n (hK : replacement_positive_limits_vanish K)
    (x : cohomology (cochain_replacement_total K) n) :
    module_hom_fun (iso_hom (replacement_filtered_total_limit_iso hK n)) x =
      module_hom_fun (iso_hom (replacement_total_limit_iso n hK)) x.
Proof.
rewrite replacement_filtered_total_limit_iso_edge replacement_filtered_second_limit_edge filtered_second_to_edge_total.
reflexivity.
Qed.

Theorem replacement_filtered_total_limit_iso_component n (hK : replacement_positive_limits_vanish K)
    (x : cohomology (cochain_replacement_total K) n) (c : C) :
    module_limit_val (module_hom_fun (iso_hom (replacement_filtered_total_limit_iso hK n)) x) c =
      cohomology_map (replacement_projection K c) n x.
Proof.
rewrite replacement_filtered_total_limit_iso_eq; exact: replacement_total_limit_iso_component.
Qed.

End Edge.
