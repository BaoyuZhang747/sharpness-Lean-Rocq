(** Actual singular-cochain replacement E2, with no assumed spectral pages. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules HomologicalModuleIso CategoryDerivedLimits.
From DiazParkV16b Require Import TopologicalCategory SingularCochainDiagrams
  SingularCochainReplacementEdge CategoryCochainFilteredSecond.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCochainDiagrams DPSingularReplacementEdge DiazParkHomologicalModuleIso.

Section Singular.
Variable Real : realType.
Variable R : pzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.

Definition singular_filtered_page r p n := replacement_filtered_page (singular_cochain_diagram Real A X) r p n.

Definition singular_filtered_second_derived_limit_iso p q : @isomorphism (module_category R)
    (singular_filtered_page 1 (Z.of_nat p) (p+q)%coq_nat)
    (derived_limit R (singular_cohomology_diagram Real A X q) p) :=
  module_iso_comp (replacement_filtered_second_derived_limit_iso (singular_cochain_diagram Real A X) p q)
    (functor_iso (derived_limit_functor R (opposite C) p)
      (singular_replacement_cohomology_iso Real A X q)).

End Singular.
