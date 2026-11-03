(** Actual collapse and its canonical total-cohomology edge for category
    cochain replacements with the literal higher-limit vanishing hypothesis. *)
From Coq Require Import Arith ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalModuleIso HomologicalDiagramInjectives.
From DiazParkV16b Require Import FilteredCochainPages FirstQuadrantFilteredPages
  FirstQuadrantFilteredVanishing FirstQuadrantFilteredCollapse FirstQuadrantFilteredGlobalCycles FirstQuadrantFilteredAbutment
  CategoryCochainReplacement CategoryCochainReplacementTotal CategoryCochainCohomologyDiagram
  CategoryCochainReplacementAcyclic CategoryCochainFilteredSecond.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso DPFilteredPages
  DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredVanishing DPFirstQuadrantFilteredCollapse
  DPFirstQuadrantFilteredGlobalCycles DPFirstQuadrantFilteredAbutment.
Local Open Scope ring_scope.

Section Collapse.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).
Variable hK : replacement_positive_limits_vanish K.

Lemma replacement_filtered_second_all_positive_zero p n
    (x : replacement_filtered_page K 1 (Z.of_nat p.+1) n) : x=0.
Proof.
destruct (le_dec p.+1 n) as [hle|hlt].
- have [q hn] : exists q, n=Nat.add p.+1 q.
    exists (Nat.sub n p.+1); lia.
  revert x; rewrite hn; intro x; exact (@replacement_filtered_second_positive_zero R C K hK p q x).
- apply: (@total_filtered_above_degree_zero R (cochain_replacement_bicomplex K) 1 (Z.of_nat p.+1) n _ x); lia.
Qed.

Theorem replacement_filtered_later_positive_zero r p n
    (x : replacement_filtered_page K r.+1 (Z.of_nat p.+1) n) : x=0.
Proof. exact: (later_positive_zero (@replacement_filtered_second_all_positive_zero) x). Qed.

Theorem replacement_filtered_later_d_zero r p n
    (x : replacement_filtered_page K r.+1 (Z.of_nat p) n) :
    total_filtered_d (cochain_replacement_bicomplex K) r.+1 (Z.of_nat p) n x=0.
Proof. exact: (later_differential_zero (@replacement_filtered_second_all_positive_zero) x). Qed.

Definition replacement_filtered_zero_column_back_iso r n :=
  zero_column_back_iso (@replacement_filtered_second_all_positive_zero) r n.

Definition replacement_filtered_total_limit_iso n : @isomorphism (module_category R)
    (cohomology (cochain_replacement_total K) n) (module_limit_type (cochain_cohomology_diagram K n)) :=
  module_iso_comp (total_zero_second_iso (@replacement_filtered_second_all_positive_zero) n)
    (replacement_filtered_second_zero_limit_iso K n).

Theorem replacement_filtered_total_limit_iso_edge n (x : cohomology (cochain_replacement_total K) n) :
    module_hom_fun (iso_hom (replacement_filtered_total_limit_iso n)) x =
      module_hom_fun (iso_hom (replacement_filtered_second_zero_limit_iso K n))
        (total_to_zero_page (cochain_replacement_bicomplex K) 1 n x).
Proof.
change (module_hom_fun (iso_hom (replacement_filtered_second_zero_limit_iso K n))
  (module_hom_fun (iso_hom (total_zero_second_iso (@replacement_filtered_second_all_positive_zero) n)) x)=
  module_hom_fun (iso_hom (replacement_filtered_second_zero_limit_iso K n))
    (total_to_zero_page (cochain_replacement_bicomplex K) 1 n x)).
by rewrite total_zero_second_iso_edge.
Qed.

End Collapse.
