(** Literal component alignment for the actual singular replacement spectral edge. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso.
From DiazParkV16b Require Import TopologicalCategory SingularCochainDiagrams SingularCochainReplacementEdge
  CategoryCochainFilteredCollapse CategoryCochainFilteredEdgeComparison SingularCochainFilteredCollapse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCochainDiagrams DPSingularReplacementEdge DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalModuleIso.

Section Edge.
Variable Real : realType.
Variable R : pzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.
Variable hX : singular_positive_limits_vanish Real A X.

Theorem singular_filtered_total_limit_iso_eq n (x : cohomology (singular_replacement_total Real A X) n) :
    module_hom_fun (iso_hom (singular_filtered_total_limit_iso hX n)) x =
      module_hom_fun (iso_hom (singular_replacement_limit_iso hX n)) x.
Proof.
change (module_hom_fun (iso_hom (functor_iso (module_limit_functor R (opposite C))
  (singular_replacement_cohomology_iso Real A X n)))
  (module_hom_fun (iso_hom (replacement_filtered_total_limit_iso (singular_replacement_positive_limits hX) n)) x)=
  module_hom_fun (iso_hom (singular_replacement_limit_iso hX n)) x).
rewrite replacement_filtered_total_limit_iso_eq; reflexivity.
Qed.

Theorem singular_filtered_total_limit_iso_component n (x : cohomology (singular_replacement_total Real A X) n) (c : C) :
    module_limit_val (module_hom_fun (iso_hom (singular_filtered_total_limit_iso hX n)) x) c =
      cohomology_map (singular_replacement_projection Real A X c) n x.
Proof.
rewrite singular_filtered_total_limit_iso_eq; exact: singular_replacement_limit_iso_component.
Qed.

End Edge.
