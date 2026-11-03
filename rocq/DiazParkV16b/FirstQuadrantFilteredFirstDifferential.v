(** Compatibility with the actual connecting-map differential on E1. *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalConnecting.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalSupport FirstQuadrantCochainSpectralFiltration
  FirstQuadrantCochainSpectralRelative FirstQuadrantCochainSpectralFirst
  FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology
  FilteredCochainPageCycleLifting FilteredCochainPageRepresentatives FilteredCochainPageKernel
  FirstQuadrantFilteredPages FirstQuadrantFilteredFirstMap FirstQuadrantFilteredFirstIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalConnecting DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantSupport
  DPColumnFiltration DPColumnRelative DPColumnFirstPage DPFilteredCycles DPFilteredPages
  DPFilteredPageHomology DPFilteredPageCycleLifting DPFilteredPageRepresentatives DPFilteredPageKernel
  DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredFirstMap DPFirstQuadrantFilteredFirstIso.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredFirstDifferential.
Section Differential.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Definition first_target_index p : Z.add (Z.of_nat p) (Z.of_nat 1)=Z.of_nat p.+1.
Proof. lia. Qed.

Definition filtered_first_d p n (x : total_filtered_page K 0 (Z.of_nat p) n) :
    total_filtered_page K 0 (Z.of_nat p.+1) n.+1 :=
  page_index_cast F 0 n.+1 (first_target_index p) (page_d F 0 (Z.of_nat p) n x).

Lemma filtered_first_d_linear p n : linear (@filtered_first_d p n).
Proof. intros a x y; by rewrite /filtered_first_d !linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (total_filtered_page K 0 (Z.of_nat p) n)
  (total_filtered_page K 0 (Z.of_nat p.+1) n.+1) _ (@filtered_first_d p n) (@filtered_first_d_linear p n).

Definition first_derivative_column p n (x : page_cycle_module F 0 (Z.of_nat p) n) : column_term K p.+1 n.+1 :=
  @submodule_in R (total_term K n.+1) (column_subspace K p.+1 n.+1) (total_d (submodule_val x))
    (proj2 (proj1 (@first_cycle_conditions R K p n (submodule_val x)) (submodule_val_mem x))).

Lemma first_derivative_cocycle p n x : cocycle (column_complex K p.+1) n.+1 (@first_derivative_column p n x).
Proof. apply submodule_val_injective; exact: total_d_squared. Qed.

Definition first_derivative_native_cycle p n x : cycle_module (column_complex K p.+1) n.+1 :=
  cycle_of_cocycle (@first_derivative_cocycle p n x).

Lemma first_native_connecting p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    couple_k K p n (first_cycle_native_class x) =
      quotient_pi (boundaries_in_cycles (column_complex K p.+1) n.+1) (first_derivative_native_cycle x).
Proof.
change (connecting_map (relative_short_exact K (filtration_succ p)) n
  (quotient_pi (boundaries_in_cycles (relative_complex K p p.+1) n) (first_cycle_native x)) =
  quotient_pi (boundaries_in_cycles (column_complex K p.+1) n.+1) (first_derivative_native_cycle x)).
rewrite connecting_map_pi.
apply: (@connecting_class_solution R (column_complex K p.+1) (column_complex K p)
  (relative_complex K p p.+1) (column_transition K (filtration_succ p))
  (relative_projection K p p.+1) (relative_short_exact K (filtration_succ p)) n
  (first_cycle_native x) (first_cycle_column K p n x) (first_derivative_native_cycle x)).
- reflexivity.
- apply submodule_val_injective; reflexivity.
Qed.

Lemma first_derivative_almost p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    almost_cycles F 1 (Z.of_nat p.+1) n.+1 (total_d (submodule_val x)).
Proof.
apply (proj2 (@first_cycle_conditions R K p.+1 n.+1 _)); split.
- exact (proj2 (proj1 (@first_cycle_conditions R K p n (submodule_val x)) (submodule_val_mem x))).
- rewrite total_d_squared; exact: subspace_zero.
Qed.

Definition first_derivative_cycle p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    page_cycle_module F 0 (Z.of_nat p.+1) n.+1 :=
  @submodule_in R (total_term K n.+1) (almost_cycles F 1 (Z.of_nat p.+1) n.+1)
    (total_d (submodule_val x)) (first_derivative_almost x).

Lemma filtered_first_d_pi p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    filtered_first_d (quotient_pi (page_denominator F 0 (Z.of_nat p) n) x) =
      quotient_pi (page_denominator F 0 (Z.of_nat p.+1) n.+1) (first_derivative_cycle x).
Proof.
rewrite /filtered_first_d page_pi_class page_d_class.
change (page_index_cast F 0 n.+1 (first_target_index p)
  (page_class (almost_cycles_d (submodule_val_mem x))) = page_class (first_derivative_almost x)).
exact: page_index_cast_class.
Qed.

Theorem filtered_first_native_differential p n (x : total_filtered_page K 0 (Z.of_nat p) n) :
    module_hom_fun (iso_hom (filtered_first_native_iso K p.+1 n.+1)) (filtered_first_d x) =
      first_d (module_hom_fun (iso_hom (filtered_first_native_iso K p n)) x).
Proof.
have [z <-] := quotient_pi_surjective x.
rewrite filtered_first_d_pi !filtered_first_native_iso_pi.
change (first_cycle_native_class (first_derivative_cycle z) =
  cohomology_map (relative_projection K p.+1 p.+2) n.+1 (couple_k K p n (first_cycle_native_class z))).
rewrite first_native_connecting cohomology_map_pi.
unfold first_cycle_native_class; f_equal; apply submodule_val_injective.
change (quotient_pi (relative_subspace K p.+1 p.+2 n.+1)
  (first_cycle_column K p.+1 n.+1 (first_derivative_cycle z)) =
  quotient_pi (relative_subspace K p.+1 p.+2 n.+1) (@first_derivative_column p n z)).
f_equal; apply submodule_val_injective; reflexivity.
Qed.

End Differential.
End DPFirstQuadrantFilteredFirstDifferential.
