(** Representative formulas for the actual E2-to-zero-column comparison. *)
From Coq Require Import Arith ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalDegreeZero HomologicalModuleIso CategoryComplexIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal FirstQuadrantCochainTotalMaps
  FirstQuadrantCochainEdge FirstQuadrantCochainSpectralFiltration FirstQuadrantCochainSpectralRelative
  FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralColumnTerms FirstQuadrantCochainSpectralColumn
  FirstQuadrantCochainSpectralColumnClasses FirstQuadrantCochainSpectralD1 FirstQuadrantCochainSpectralSecond
  CochainDegreeTransport CochainSignTwist CochainZeroCycleNaturality SubquotientModuleIso
  FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology FilteredCochainPageCycleLifting
  FilteredCochainPageKernel FilteredCochainPageIteration FirstQuadrantFilteredPages FirstQuadrantFilteredFirstMap
  FirstQuadrantFilteredFirstIso FirstQuadrantFilteredSecondRow FirstQuadrantFilteredSecondIso FirstQuadrantFilteredGlobalCycles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalDegreeZero
  DiazParkHomologicalModuleIso DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps DPFirstQuadrantEdge
  DPColumnFiltration DPColumnRelative DPColumnFirstPage DPColumnCoordinate DPColumnFirstIdentification DPColumnFirstClasses
  DPColumnD1 DPColumnSecondPage DPCochainDegreeTransport DPCochainSignTwist DPCochainZeroCycleNaturality DPSubquotientModuleIso
  DPFilteredCycles DPFilteredPages DPFilteredPageHomology DPFilteredPageCycleLifting DPFilteredPageKernel DPFilteredPageIteration
  DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredFirstMap DPFirstQuadrantFilteredFirstIso
  DPFirstQuadrantFilteredSecondRow DPFirstQuadrantFilteredSecondIso DPFirstQuadrantFilteredGlobalCycles.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredEdgeRepresentatives.
Section Representatives.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Lemma filtered_second_zero_first n (x : page_cycle_module F 1 0 n) :
    submodule_val (cohomology_zero_cycle (first_page_row K n)
      (module_hom_fun (iso_hom (filtered_second_native_iso K 0 n)) (quotient_pi (page_denominator F 1 0 n) x))) =
    module_hom_fun (iso_hom (@cohomology_degree_iso R (relative_complex K 0 1) n (n+0)%coq_nat (Nat.add_comm 0 n)))
      (@first_cycle_native_class R K 0 n (next_cycle_to_old_cycle F 0 0 n x)).
Proof.
change (submodule_val (cohomology_zero_cycle (first_page_row K n)
  (cohomology_map (term_iso_cochain_map (@first_row_swapped_commutes R K n)) 0
    (module_hom_fun (iso_hom (first_page_homology_row_iso K 0 n))
      (module_hom_fun (iso_hom (next_page_homology_iso F 0 0 n)) (quotient_pi (page_denominator F 1 0 n) x))))) =
  module_hom_fun (iso_hom (@cohomology_degree_iso R (relative_complex K 0 1) n (n+0)%coq_nat (Nat.add_comm 0 n)))
    (@first_cycle_native_class R K 0 n (next_cycle_to_old_cycle F 0 0 n x))).
rewrite next_page_homology_iso_pi /next_cycle_to_homology /first_page_homology_row_iso subquotient_iso_pi.
rewrite /subquotient_class_map cohomology_map_pi cohomology_zero_cycle_pi.
change (module_hom_fun (iso_hom (first_row_swapped_term_iso K n 0))
  (module_hom_fun (iso_hom (filtered_first_native_iso K 0 n)) (next_cycle_to_page x)) =
  module_hom_fun (iso_hom (first_row_swapped_term_iso K n 0))
    (@first_cycle_native_class R K 0 n (next_cycle_to_old_cycle F 0 0 n x))).
by rewrite /next_cycle_to_page filtered_first_native_iso_pi.
Qed.

Lemma second_horizontal_zero_val n (x : second_page K 0 n) :
    submodule_val (cohomology_zero_cycle (horizontal_cohomology_row K n)
      (module_hom_fun (iso_hom (second_page_horizontal_iso K 0 n)) x)) =
    module_hom_fun (iso_hom (first_page_column_iso K 0 n))
      (submodule_val (cohomology_zero_cycle (first_page_row K n) x)).
Proof.
change (submodule_val (cohomology_zero_cycle (horizontal_cohomology_row K n)
  (cohomology_map (sign_twist_cochain_map (horizontal_cohomology_row K n) n) 0
    (cohomology_map (term_iso_cochain_map (@first_page_row_term_commutes R K n)) 0 x))) =
  module_hom_fun (iso_hom (first_page_column_iso K 0 n))
    (submodule_val (cohomology_zero_cycle (first_page_row K n) x))).
rewrite !cohomology_zero_cycle_map_val.
change ((-1:R)^+(n*0)%N *: module_hom_fun (iso_hom (first_page_column_iso K 0 n))
  (submodule_val (cohomology_zero_cycle (first_page_row K n) x)) =
  module_hom_fun (iso_hom (first_page_column_iso K 0 n))
    (submodule_val (cohomology_zero_cycle (first_page_row K n) x))).
by rewrite muln0 expr0 scale1r.
Qed.

Lemma relative_term_cast_pi p q n m (h:n=m) (x : column_term K p n) :
    @term_cast R (relative_complex K p q) n m h (quotient_pi (relative_subspace K p q n) x)=
      quotient_pi (relative_subspace K p q m) (@term_cast R (column_complex K p) n m h x).
Proof. destruct h; reflexivity. Qed.

Lemma first_native_global_vertical n (z : cycle_module (total_complex K) n) :
    module_hom_fun (iso_hom (first_page_column_iso K 0 n))
      (module_hom_fun (iso_hom (@cohomology_degree_iso R (relative_complex K 0 1) n (n+0)%coq_nat (Nat.add_comm 0 n)))
        (@first_cycle_native_class R K 0 n (global_cycle_to_filtered K 0 n z))) =
    cohomology_map (zero_column_projection K) n (quotient_pi (boundaries_in_cycles (total_complex K) n) z).
Proof.
rewrite /first_cycle_native_class cohomology_degree_iso_pi first_page_column_iso_class cohomology_map_pi.
f_equal; apply submodule_val_injective.
rewrite first_page_vertical_cycle_val mul0n expr0 scale1r cycle_cast_val.
change (module_hom_fun (iso_hom (column_coordinate_iso K 0 n))
  (@term_cast R (relative_complex K 0 1) n (n+0)%coq_nat (Nat.add_comm 0 n)
    (quotient_pi (relative_subspace K 0 1 n) (first_cycle_column K 0 n (global_cycle_to_filtered K 0 n z)))) =
  zero_column_at (submodule_val z)).
rewrite relative_term_cast_pi column_coordinate_iso_pi /column_coordinate column_cast_coordinate.
change (submodule_val z 0 n (Logic.eq_trans (Nat.add_comm 0 n) (Logic.eq_sym (Nat.add_comm 0 n))) =
  submodule_val z 0 n Logic.eq_refl).
have he : Logic.eq_trans (Nat.add_comm 0 n) (Logic.eq_sym (Nat.add_comm 0 n))=Logic.eq_refl by apply Prop_irrelevance.
by rewrite he.
Qed.

End Representatives.
End DPFirstQuadrantFilteredEdgeRepresentatives.
