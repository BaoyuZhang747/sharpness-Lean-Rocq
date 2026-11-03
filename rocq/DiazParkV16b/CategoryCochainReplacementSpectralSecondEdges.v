(** The zero column and positive-column vanishing on the constructed E2.
    This does not claim any unconstructed later-page differential vanishes. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness CategoryModuleLimits
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalDiagramInjectives HomologicalModuleIso BarDegreeZero.
From DiazParkV16b Require Import CategoryCochainCohomologyDiagram
  CategoryCochainReplacementAcyclic CategoryCochainReplacementSpectralSecond.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DiazParkBarDegreeZero.
Local Open Scope ring_scope.

Section SecondEdges.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).

Definition replacement_second_page_zero_limit_iso q : @isomorphism (module_category R)
    (replacement_second_page K 0%N q) (module_limit_type (cochain_cohomology_diagram K q)) :=
  module_iso_comp (replacement_second_page_bar_iso K 0%N q)
    (bar_zero_cohomology_limit_iso (cochain_cohomology_diagram K q)).

Theorem replacement_second_page_positive_zero
    (hK : replacement_positive_limits_vanish K) p q (x : replacement_second_page K p.+1 q) : x = 0.
Proof.
apply (module_iso_hom_injective (e := replacement_second_page_derived_limit_iso K p.+1 q)).
rewrite module_hom_zero; exact: hK.
Qed.

End SecondEdges.
