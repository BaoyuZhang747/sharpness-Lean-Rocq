(** All actual pages are supported in the first quadrant. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology FirstQuadrantFilteredPages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFirstQuadrantCochain DPFirstQuadrantTotal
  DPFilteredCycles DPFilteredPages DPFilteredPageHomology DPFirstQuadrantFilteredPages.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredVanishing.
Section Vanishing.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Theorem total_filtered_negative_zero r p n (h : Z.lt p 0) (x : page F r p n) : x=0.
Proof.
have [z <-] := quotient_pi_surjective x.
apply/(quotient_pi_kernel (page_denominator F r p n) z).
apply page_relations_next; split.
- apply: (@total_column_filtration_nonpositive R K (Z.succ p) n _ (submodule_val z)); lia.
- change (filtration F (Z.add (Z.succ p) (Z.of_nat r)) n.+1 (total_d (submodule_val z))).
  have he : Z.add (Z.succ p) (Z.of_nat r)=Z.add p (Z.of_nat r.+1) by lia.
  rewrite he; exact (proj2 (submodule_val_mem z)).
Qed.

Theorem total_filtered_above_degree_zero r p n (h : Z.lt (Z.of_nat n) p) (x : page F r p n) : x=0.
Proof.
have [z <-] := quotient_pi_surjective x.
have hz : z=0.
  apply submodule_val_injective; exact (@total_column_filtration_bounded R K p n h _ (proj1 (submodule_val_mem z))).
by rewrite hz linear0.
Qed.

Theorem total_filtered_zero_boundaries r n (x : page F r 0 n) : page_boundaries F r 0 n x -> x=0.
Proof.
destruct n; [exact (fun h => h)|].
intros [y <-].
have hy : y=0 := @total_filtered_negative_zero r (Z.sub 0 (Z.of_nat r.+1)) n (ltac:(lia)) y.
change (page_incoming y=0); by rewrite hy linear0.
Qed.

End Vanishing.
End DPFirstQuadrantFilteredVanishing.
