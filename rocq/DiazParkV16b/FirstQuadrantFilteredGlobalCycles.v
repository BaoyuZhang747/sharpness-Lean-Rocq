(** The canonical edge from actual total cohomology to every zero-column
    page, and compatibility with the actual page-to-page maps. *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps
  HomologicalComplex HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FilteredCochainCycles FilteredCochainPages FilteredCochainPageCycleLifting
  FirstQuadrantFilteredPages FirstQuadrantFilteredCollapse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFilteredCycles DPFilteredPages DPFilteredPageCycleLifting
  DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredCollapse.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredGlobalCycles.
Section Global.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Lemma global_cycle_almost r n x (hx : cycle_subspace (total_complex K) n x) : almost_cycles F r 0 n x.
Proof.
split; [exact (@total_column_filtration_nonpositive R K 0 n (Z.le_refl 0) x)|].
change (filtration F (Z.add 0 (Z.of_nat r)) n.+1 (total_d x)).
change (total_d x=0) in hx; rewrite hx; exact: subspace_zero.
Qed.

Definition global_cycle_to_filtered r n : {linear cycle_module (total_complex K) n -> page_cycle_module F r 0 n} :=
  @submodule_map R (total_term K n) (total_term K n) (idfun : {linear _ -> _})
    (cycle_subspace (total_complex K) n) (almost_cycles F r.+1 0 n) (@global_cycle_almost r.+1 n).

Definition global_cycle_page r n (x : cycle_module (total_complex K) n) : page F r 0 n :=
  quotient_pi (page_denominator F r 0 n) (global_cycle_to_filtered r n x).

Lemma global_cycle_page_linear r n : linear (@global_cycle_page r n).
Proof. intros a x y; by rewrite /global_cycle_page !linearP. Qed.
HB.instance Definition _ r n := GRing.isLinear.Build R (cycle_module (total_complex K) n) (page F r 0 n) _
  (@global_cycle_page r n) (@global_cycle_page_linear r n).

Lemma global_cycle_page_boundaries r n x : boundaries_in_cycles (total_complex K) n x -> global_cycle_page r x=0.
Proof.
intro hx; rewrite /global_cycle_page quotient_pi_kernel.
apply page_relations_boundary; split.
- exact (@total_column_filtration_nonpositive R K 0 n (Z.le_refl 0) (submodule_val x)).
- have hc := proj1 (@boundary_subspaceE R (total_complex K) n (submodule_val x)) hx.
  destruct n; [exact hc|].
  destruct hc as [v hv]; exists v; split; [|exact hv].
  apply: (@total_column_filtration_nonpositive R K (Z.sub 0 (Z.of_nat r)) n _ v); lia.
Qed.

Definition total_to_zero_page r n : {linear cohomology (total_complex K) n -> page F r 0 n} :=
  @quotient_lift R (cycle_module (total_complex K) n) (boundaries_in_cycles (total_complex K) n) (page F r 0 n)
    (@global_cycle_page r n) (@global_cycle_page_boundaries r n).

Lemma total_to_zero_page_pi r n x : total_to_zero_page r n (quotient_pi (boundaries_in_cycles (total_complex K) n) x)=
    global_cycle_page r x.
Proof. exact: quotient_lift_pi. Qed.

Variable h2 : forall p n (x : page F 1 (Z.of_nat p.+1) n), x=0.

Lemma zero_column_step_global_cycle r n (x : cycle_module (total_complex K) n) :
    module_hom_fun (iso_hom (zero_column_step_iso h2 r n)) (global_cycle_page r.+2 x)=global_cycle_page r.+1 x.
Proof.
rewrite /global_cycle_page zero_column_step_iso_pi /next_cycle_to_page.
f_equal; apply submodule_val_injective; reflexivity.
Qed.

Lemma zero_column_back_global_cycle r n (x : cycle_module (total_complex K) n) :
    module_hom_fun (iso_hom (zero_column_back_iso h2 r n)) (global_cycle_page r.+1 x)=global_cycle_page 1 x.
Proof.
induction r as [|r ihr]; [reflexivity|].
change (module_hom_fun (iso_hom (zero_column_back_iso h2 r n))
  (module_hom_fun (iso_hom (zero_column_step_iso h2 r n)) (global_cycle_page r.+2 x))=global_cycle_page 1 x).
by rewrite zero_column_step_global_cycle ihr.
Qed.

Lemma zero_column_back_total r n (x : cohomology (total_complex K) n) :
    module_hom_fun (iso_hom (zero_column_back_iso h2 r n)) (total_to_zero_page r.+1 n x)=total_to_zero_page 1 n x.
Proof.
have [z <-] := quotient_pi_surjective x.
rewrite !total_to_zero_page_pi; exact: zero_column_back_global_cycle.
Qed.

End Global.
End DPFirstQuadrantFilteredGlobalCycles.
