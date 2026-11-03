(** The elementary all-degree edge isomorphism for the actual first-quadrant
    total, retaining its literal zero-column projection. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainEdge FirstQuadrantCochainEdgeInjective
  FirstQuadrantCochainEdgeSurjective.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps DPFirstQuadrantEdge
  DPFirstQuadrantEdgeInjective DPFirstQuadrantEdgeSurjective.

Module DPFirstQuadrantEdgeComparison.
Section Comparison.
Variable R : pzRingType.
Variable K : bicomplex R.
Variable hK : positive_horizontal_exact K.

Definition edge_iso n : @isomorphism (module_category R)
    (cohomology (total_complex K) n) (edge_module K n) :=
  @linear_bijection_iso R (cohomology (total_complex K) n) (edge_module K n)
    (edge_map K n) (@edge_map_injective R K hK n) (@edge_map_surjective R K hK n).

Theorem edge_iso_hom n (x : cohomology (total_complex K) n) :
    module_hom_fun (iso_hom (edge_iso n)) x = edge_map K n x.
Proof. reflexivity. Qed.

Theorem edge_iso_component n (x : cohomology (total_complex K) n) :
    submodule_val (module_hom_fun (iso_hom (edge_iso n)) x) =
      cohomology_map (zero_column_projection K) n x.
Proof. reflexivity. Qed.
End Comparison.
End DPFirstQuadrantEdgeComparison.
