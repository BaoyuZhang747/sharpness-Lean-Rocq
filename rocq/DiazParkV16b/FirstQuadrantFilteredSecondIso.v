(** The actual E2 subquotient is the native cohomology of the first-page row.
    In column zero the negative-column incoming module is proved zero. *)
From Coq Require Import Arith ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex
  HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralSecond
  FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology FilteredCochainPageIteration
  FilteredCochainPageIndexTransport SubquotientModuleIso FirstQuadrantFilteredPages
  FirstQuadrantFilteredFirstIso FirstQuadrantFilteredFirstDifferential FirstQuadrantFilteredFirstIncoming
  FirstQuadrantFilteredSecondRow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPColumnFirstPage DPColumnSecondPage DPFilteredCycles DPFilteredPages
  DPFilteredPageHomology DPFilteredPageIteration DPFilteredPageIndexTransport DPSubquotientModuleIso
  DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredFirstIso DPFirstQuadrantFilteredFirstDifferential
  DPFirstQuadrantFilteredFirstIncoming DPFirstQuadrantFilteredSecondRow.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredSecondIso.
Section Iso.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Lemma filtered_first_cycle_iff p n (x : page F 0 (Z.of_nat p) n) :
    page_d F 0 (Z.of_nat p) n x=0 <->
      first_d (module_hom_fun (iso_hom (filtered_first_native_iso K p n)) x)=0.
Proof.
rewrite -filtered_first_native_differential; split.
- intro hx; by rewrite /filtered_first_d hx linear0 module_hom_zero.
- intro hx.
  have hc : filtered_first_d x=0.
    apply (module_iso_hom_injective (e:=filtered_first_native_iso K p.+1 n.+1)); by rewrite module_hom_zero.
  apply (@page_index_cast_injective R (total_complex K) F 0 _ _ n.+1 (first_target_index p)).
  change (filtered_first_d x=page_index_cast F 0 n.+1 (first_target_index p) 0).
  by rewrite linear0.
Qed.

Lemma filtered_first_row_cycles p q x :
    linear_kernel (page_d F 0 (Z.of_nat p) (p+q)%coq_nat) x <->
      cycle_subspace (first_page_row_swapped K q) p
        (module_hom_fun (iso_hom (filtered_first_native_iso K p (p+q)%coq_nat)) x).
Proof. exact: filtered_first_cycle_iff. Qed.

Lemma filtered_first_row_boundaries p q x :
    page_boundaries F 0 (Z.of_nat p) (p+q)%coq_nat x <->
      boundary_subspace (first_page_row_swapped K q) p
        (module_hom_fun (iso_hom (filtered_first_native_iso K p (p+q)%coq_nat)) x).
Proof.
destruct p.
- change (page_boundaries F 0 0 q x <-> module_hom_fun (iso_hom (filtered_first_native_iso K 0 q)) x=0).
  rewrite filtered_first_zero_boundaries; split; [intro hx; by rewrite hx module_hom_zero|].
  intro hx; apply (module_iso_hom_injective (e:=filtered_first_native_iso K 0 q)); by rewrite module_hom_zero.
- split.
  + intros [y hy].
    exists (module_hom_fun (iso_hom (first_incoming_native_iso K p (p+q)%coq_nat)) y).
    change (first_d (module_hom_fun (iso_hom (first_incoming_native_iso K p (p+q)%coq_nat)) y) =
      module_hom_fun (iso_hom (filtered_first_native_iso K p.+1 (p.+1+q)%coq_nat)) x).
    rewrite -first_incoming_native_differential.
    change (page_incoming y=x) in hy; by rewrite hy.
  + intros [y hy].
    exists (module_hom_fun (iso_inv (first_incoming_native_iso K p (p+q)%coq_nat)) y).
    apply (module_iso_hom_injective (e:=filtered_first_native_iso K p.+1 (p.+1+q)%coq_nat)).
    change (module_hom_fun (iso_hom (filtered_first_native_iso K p.+1 (p+q)%coq_nat.+1))
      (page_incoming (module_hom_fun (iso_inv (first_incoming_native_iso K p (p+q)%coq_nat)) y)) =
      module_hom_fun (iso_hom (filtered_first_native_iso K p.+1 (p.+1+q)%coq_nat)) x).
    rewrite first_incoming_native_differential module_iso_inv_hom_apply; exact hy.
Qed.

Definition first_page_homology_row_iso p q : @isomorphism (module_category R)
    (page_homology F 0 (Z.of_nat p) (p+q)%coq_nat) (cohomology (first_page_row_swapped K q) p) :=
  @subquotient_iso R (page F 0 (Z.of_nat p) (p+q)%coq_nat) (first_page K p (p+q)%coq_nat)
    (linear_kernel (page_d F 0 (Z.of_nat p) (p+q)%coq_nat)) (page_boundaries F 0 (Z.of_nat p) (p+q)%coq_nat)
    (cycle_subspace (first_page_row_swapped K q) p) (boundary_subspace (first_page_row_swapped K q) p)
    (filtered_first_native_iso K p (p+q)%coq_nat) (@filtered_first_row_cycles p q) (@filtered_first_row_boundaries p q).

Definition filtered_second_native_iso p q : @isomorphism (module_category R)
    (total_filtered_page K 1 (Z.of_nat p) (p+q)%coq_nat) (second_page K p q) :=
  module_iso_comp (next_page_homology_iso F 0 (Z.of_nat p) (p+q)%coq_nat)
    (module_iso_comp (first_page_homology_row_iso p q) (first_row_swapped_cohomology_iso K q p)).

End Iso.
End DPFirstQuadrantFilteredSecondIso.
