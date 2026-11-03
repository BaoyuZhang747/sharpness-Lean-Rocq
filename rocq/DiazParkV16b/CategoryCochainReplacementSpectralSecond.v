(** The actual second page of a category cochain replacement is the native
    right-derived limit of its objectwise cohomology diagram. The page and
    its differential were constructed from the literal column filtration. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalDiagramInjectives HomologicalCohomology
  HomologicalModuleIso CategoryComplexIso CategoryDerivedLimits BarComplex BarDerivedComparison.
From DiazParkV16b Require Import FirstQuadrantCochainEdge FirstQuadrantCochainSpectralSecond
  CategoryCochainReplacement CategoryCochainCohomologyDiagram CategoryCochainReplacementVertical
  CategoryCochainReplacementHorizontal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DiazParkBarComplex DiazParkBarDerivedComparison DPFirstQuadrantEdge DPColumnSecondPage.

Section ReplacementSecond.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).

Definition replacement_cohomology_row_term_iso q p : @isomorphism (module_category R)
    (cochain_term (horizontal_cohomology_row (cochain_replacement_bicomplex K) q) p)
    (cochain_term (bar_complex (cochain_cohomology_diagram K q)) p) :=
  replacement_vertical_cohomology_iso K p q.

Lemma replacement_cohomology_row_term_commutes q p x :
    cochain_d (bar_complex (cochain_cohomology_diagram K q)) p
      (module_hom_fun (iso_hom (replacement_cohomology_row_term_iso q p)) x) =
    module_hom_fun (iso_hom (replacement_cohomology_row_term_iso q p.+1))
      (cochain_d (horizontal_cohomology_row (cochain_replacement_bicomplex K) q) p x).
Proof. symmetry; exact: replacement_vertical_cohomology_horizontal. Qed.

Definition replacement_cohomology_row_map q :=
  term_iso_cochain_map (@replacement_cohomology_row_term_commutes q).

Definition replacement_second_page p q : lmodType R := second_page (cochain_replacement_bicomplex K) p q.

Definition replacement_second_page_bar_iso p q : @isomorphism (module_category R)
    (replacement_second_page p q) (cohomology (bar_complex (cochain_cohomology_diagram K q)) p) :=
  module_iso_comp (second_page_horizontal_iso (cochain_replacement_bicomplex K) p q)
    (term_iso_cohomology_iso (@replacement_cohomology_row_term_commutes q) p).

Definition replacement_second_page_derived_limit_iso p q : @isomorphism (module_category R)
    (replacement_second_page p q) (derived_limit R (cochain_cohomology_diagram K q) p) :=
  module_iso_comp (replacement_second_page_bar_iso p q)
    (bar_derived_limit_iso (cochain_cohomology_diagram K q) p).

End ReplacementSecond.
