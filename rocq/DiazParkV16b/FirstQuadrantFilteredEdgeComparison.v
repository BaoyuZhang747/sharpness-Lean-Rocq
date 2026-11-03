(** The canonical spectral edge is the literal zero-column cohomology map. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalDegreeZero HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal FirstQuadrantCochainTotalMaps
  FirstQuadrantCochainEdge FirstQuadrantCochainSpectralColumn FirstQuadrantCochainSpectralSecond
  FilteredCochainPages FilteredCochainPageCycleLifting FirstQuadrantFilteredPages FirstQuadrantFilteredSecondIso
  FirstQuadrantFilteredGlobalCycles FirstQuadrantFilteredEdgeRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalDegreeZero
  DiazParkHomologicalModuleIso DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps DPFirstQuadrantEdge
  DPColumnFirstIdentification DPColumnSecondPage DPFilteredPages DPFilteredPageCycleLifting DPFirstQuadrantFilteredPages
  DPFirstQuadrantFilteredSecondIso DPFirstQuadrantFilteredGlobalCycles DPFirstQuadrantFilteredEdgeRepresentatives.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredEdgeComparison.
Section Edge.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Definition filtered_second_to_edge n (x : total_filtered_page K 1 0 n) : edge_module K n :=
  cohomology_zero_cycle (horizontal_cohomology_row K n)
    (module_hom_fun (iso_hom (second_page_horizontal_iso K 0 n))
      (module_hom_fun (iso_hom (filtered_second_native_iso K 0 n)) x)).

Lemma filtered_second_to_edge_global n (z : cycle_module (total_complex K) n) :
    submodule_val (filtered_second_to_edge (@global_cycle_page R K 1 n z)) =
      cohomology_map (zero_column_projection K) n (quotient_pi (boundaries_in_cycles (total_complex K) n) z).
Proof.
rewrite /filtered_second_to_edge second_horizontal_zero_val /global_cycle_page filtered_second_zero_first.
have he : next_cycle_to_old_cycle F 0 0 n (global_cycle_to_filtered K 1 n z)=global_cycle_to_filtered K 0 n z.
  apply submodule_val_injective; reflexivity.
rewrite he; exact: first_native_global_vertical.
Qed.

Theorem filtered_second_to_edge_total n (x : cohomology (total_complex K) n) :
    filtered_second_to_edge (total_to_zero_page K 1 n x)=edge_map K n x.
Proof.
apply submodule_val_injective.
have [z <-] := quotient_pi_surjective x.
rewrite total_to_zero_page_pi filtered_second_to_edge_global; reflexivity.
Qed.

End Edge.
End DPFirstQuadrantFilteredEdgeComparison.
