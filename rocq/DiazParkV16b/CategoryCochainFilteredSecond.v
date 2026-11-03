(** The E2 page of the genuine all-page filtered-cycle construction computes
    native higher limits of the actual objectwise cohomology diagram. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness CategoryModuleLimits
  HomologicalDiagramInjectives HomologicalModuleIso CategoryDerivedLimits.
From DiazParkV16b Require Import CategoryCochainReplacement CategoryCochainCohomologyDiagram
  CategoryCochainReplacementAcyclic CategoryCochainReplacementSpectralSecond
  CategoryCochainReplacementSpectralSecondEdges FirstQuadrantFilteredPages FirstQuadrantFilteredSecondIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredSecondIso.
Local Open Scope ring_scope.

Section Replacement.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).

Definition replacement_filtered_page r p n := total_filtered_page (cochain_replacement_bicomplex K) r p n.

Definition replacement_filtered_second_derived_limit_iso p q : @isomorphism (module_category R)
    (replacement_filtered_page 1 (Z.of_nat p) (p+q)%coq_nat)
    (derived_limit R (cochain_cohomology_diagram K q) p) :=
  module_iso_comp (filtered_second_native_iso (cochain_replacement_bicomplex K) p q)
    (replacement_second_page_derived_limit_iso K p q).

Definition replacement_filtered_second_zero_limit_iso q : @isomorphism (module_category R)
    (replacement_filtered_page 1 0 q) (module_limit_type (cochain_cohomology_diagram K q)) :=
  module_iso_comp (filtered_second_native_iso (cochain_replacement_bicomplex K) 0 q)
    (replacement_second_page_zero_limit_iso K q).

Theorem replacement_filtered_second_positive_zero (hK : replacement_positive_limits_vanish K) p q
    (x : replacement_filtered_page 1 (Z.of_nat p.+1) (p.+1+q)%coq_nat) : x=0.
Proof.
apply (module_iso_hom_injective (e:=replacement_filtered_second_derived_limit_iso p.+1 q)).
rewrite module_hom_zero; exact: hK.
Qed.

End Replacement.
