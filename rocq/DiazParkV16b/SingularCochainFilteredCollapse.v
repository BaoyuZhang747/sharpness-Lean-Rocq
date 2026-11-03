(** Actual collapse of the unnormalized singular-cochain replacement model. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import TopologicalCategory SingularCochainDiagrams SingularCochainReplacementEdge
  CategoryCochainReplacement CategoryCochainFilteredCollapse SingularCochainFilteredSecond FirstQuadrantFilteredPages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPTopological DPSingularCochainDiagrams DPSingularReplacementEdge DiazParkHomological DiazParkCohomology
  DiazParkHomologicalModuleIso DPFirstQuadrantFilteredPages.
Local Open Scope ring_scope.

Section Singular.
Variable Real : realType.
Variable R : pzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.
Variable hX : singular_positive_limits_vanish Real A X.

Theorem singular_filtered_later_positive_zero r p n
    (x : singular_filtered_page Real A X r.+1 (Z.of_nat p.+1) n) : x=0.
Proof. exact: (replacement_filtered_later_positive_zero (singular_replacement_positive_limits hX) x). Qed.

Theorem singular_filtered_later_d_zero r p n
    (x : singular_filtered_page Real A X r.+1 (Z.of_nat p) n) :
    total_filtered_d (cochain_replacement_bicomplex (singular_cochain_diagram Real A X)) r.+1 (Z.of_nat p) n x=0.
Proof. exact: (replacement_filtered_later_d_zero (singular_replacement_positive_limits hX) x). Qed.

Definition singular_filtered_zero_column_back_iso r n :=
  replacement_filtered_zero_column_back_iso (singular_replacement_positive_limits hX) r n.

Definition singular_filtered_total_limit_iso n : @isomorphism (module_category R)
    (cohomology (singular_replacement_total Real A X) n)
    (module_limit_type (singular_cohomology_diagram Real A X n)) :=
  module_iso_comp (replacement_filtered_total_limit_iso (singular_replacement_positive_limits hX) n)
    (functor_iso (module_limit_functor R (opposite C)) (singular_replacement_cohomology_iso Real A X n)).

End Singular.
