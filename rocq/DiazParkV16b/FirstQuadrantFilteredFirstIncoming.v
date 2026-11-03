(** The zero-column incoming image and actual positive-column incoming maps. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainSpectralFirst FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology
  FilteredCochainPageIndexTransport FirstQuadrantFilteredPages FirstQuadrantFilteredFirstIso FirstQuadrantFilteredFirstDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPColumnFirstPage DPFilteredCycles DPFilteredPages
  DPFilteredPageHomology DPFilteredPageIndexTransport DPFirstQuadrantFilteredPages
  DPFirstQuadrantFilteredFirstIso DPFirstQuadrantFilteredFirstDifferential.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredFirstIncoming.
Section Incoming.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Theorem filtered_first_negative_zero p n (hp : Z.lt p 0) (x : page F 0 p n) : x=0.
Proof.
have [z <-] := quotient_pi_surjective x.
apply/(quotient_pi_kernel (page_denominator F 0 p n) z).
apply page_relations_next; split.
- apply: (@total_column_filtration_nonpositive R K (Z.succ p) n _ (submodule_val z)); lia.
- change (filtration F (Z.add (Z.succ p) 0) n.+1 (total_d (submodule_val z))).
  rewrite Z.add_0_r; apply: (@total_column_filtration_nonpositive R K (Z.succ p) n.+1 _ _); lia.
Qed.

Lemma filtered_first_zero_boundaries n (x : page F 0 0 n) : page_boundaries F 0 0 n x <-> x=0.
Proof.
split.
- destruct n; [exact (fun h => h)|].
  intros [y <-].
  have hy : y=0 := @filtered_first_negative_zero (Z.sub 0 (Z.of_nat 1)) n (ltac:(lia)) y.
  change (page_incoming y=0); by rewrite hy linear0.
- intro hx; rewrite hx; exact: subspace_zero.
Qed.

Definition first_source_index p : Z.sub (Z.of_nat p.+1) (Z.of_nat 1)=Z.of_nat p.
Proof. lia. Qed.

Definition first_incoming_native_iso p n : @isomorphism (module_category R)
    (page F 0 (Z.sub (Z.of_nat p.+1) (Z.of_nat 1)) n) (first_page K p n) :=
  module_iso_comp (page_index_iso F 0 n (first_source_index p)) (filtered_first_native_iso K p n).

Lemma first_incoming_native_differential p n (x : page F 0 (Z.sub (Z.of_nat p.+1) (Z.of_nat 1)) n) :
    module_hom_fun (iso_hom (filtered_first_native_iso K p.+1 n.+1)) (page_incoming x) =
      first_d (module_hom_fun (iso_hom (first_incoming_native_iso p n)) x).
Proof.
rewrite (@page_incoming_after_cast R (total_complex K) F 0 (Z.of_nat p.+1) (Z.of_nat p) n
  (first_source_index p) (first_target_index p) x).
change (module_hom_fun (iso_hom (filtered_first_native_iso K p.+1 n.+1))
  (filtered_first_d (page_index_cast F 0 n (first_source_index p) x)) =
  first_d (module_hom_fun (iso_hom (filtered_first_native_iso K p n))
    (module_hom_fun (iso_hom (page_index_iso F 0 n (first_source_index p))) x))).
rewrite page_index_iso_hom; exact: filtered_first_native_differential.
Qed.

End Incoming.
End DPFirstQuadrantFilteredFirstIncoming.
