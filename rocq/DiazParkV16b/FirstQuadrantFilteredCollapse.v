(** Actual collapse from E2 positive-column vanishing. All later pages and
    zero-column comparison maps are derived from the native page homology. *)
From Coq Require Import Arith ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology
  FilteredCochainPageCycleLifting FilteredCochainPageKernel FilteredCochainPageIteration FilteredCochainPageCollapse
  FirstQuadrantFilteredPages FirstQuadrantFilteredVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalModuleIso DPFirstQuadrantCochain DPFirstQuadrantTotal
  DPFilteredCycles DPFilteredPages DPFilteredPageHomology DPFilteredPageCycleLifting DPFilteredPageKernel
  DPFilteredPageIteration DPFilteredPageCollapse DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredVanishing.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredCollapse.
Section Collapse.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.
Hypothesis h2 : forall p n (x : page F 1 (Z.of_nat p.+1) n), x=0.

Theorem later_positive_zero r p n (x : page F r.+1 (Z.of_nat p.+1) n) : x=0.
Proof.
induction r as [|r ihr].
- exact: h2.
- apply (module_iso_hom_injective (e:=next_page_homology_iso F r.+1 (Z.of_nat p.+1) n)).
  rewrite module_hom_zero.
  apply (@page_homology_zero_of_page_zero R (total_complex K) F r.+1 (Z.of_nat p.+1) n).
  exact ihr.
Qed.

Theorem later_differential_zero r p n (x : page F r.+1 (Z.of_nat p) n) : page_d F r.+1 (Z.of_nat p) n x=0.
Proof.
have he : Z.add (Z.of_nat p) (Z.of_nat r.+2)=Z.of_nat (p+r+1)%coq_nat.+1.
  rewrite !Nat2Z.inj_succ !Nat2Z.inj_add; lia.
have hz : forall z : page F r.+1 (Z.add (Z.of_nat p) (Z.of_nat r.+2)) n.+1, z=0.
  rewrite he; exact: later_positive_zero.
exact: hz.
Qed.

Definition zero_column_step_iso r n : @isomorphism (module_category R)
    (page F r.+2 0 n) (page F r.+1 0 n) :=
  module_iso_comp (next_page_homology_iso F r.+1 0 n)
    (@page_homology_zero_differentials_iso R (total_complex K) F r.+1 0 n
      (@later_differential_zero r 0 n) (@total_filtered_zero_boundaries R K r.+1 n)).

Lemma zero_column_step_iso_pi r n (x : page_cycle_module F r.+2 0 n) :
    module_hom_fun (iso_hom (zero_column_step_iso r n))
      (quotient_pi (page_denominator F r.+2 0 n) x)=next_cycle_to_page x.
Proof.
change (module_hom_fun (iso_hom (@page_homology_zero_differentials_iso R (total_complex K) F r.+1 0 n
  (@later_differential_zero r 0 n) (@total_filtered_zero_boundaries R K r.+1 n)))
  (module_hom_fun (iso_hom (next_page_homology_iso F r.+1 0 n))
    (quotient_pi (page_denominator F r.+2 0 n) x))=next_cycle_to_page x).
rewrite next_page_homology_iso_pi /next_cycle_to_homology page_homology_zero_differentials_iso_pi; reflexivity.
Qed.

Fixpoint zero_column_back_iso r n : @isomorphism (module_category R) (page F r.+1 0 n) (page F 1 0 n) :=
  match r as s return @isomorphism (module_category R) (page F s.+1 0 n) (page F 1 0 n) with
  | O => iso_refl _
  | S s => module_iso_comp (zero_column_step_iso s n) (zero_column_back_iso s n)
  end.

End Collapse.
End DPFirstQuadrantFilteredCollapse.
