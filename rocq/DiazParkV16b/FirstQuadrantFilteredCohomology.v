(** The abutment filtration is literally the image of H(Fp Tot)->H(Tot). *)
From Coq Require Import Arith ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalSupport FirstQuadrantCochainSpectralFiltration
  FilteredCochainCycles FilteredCochainCohomologyFiltration FirstQuadrantFilteredPages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantSupport DPColumnFiltration DPFilteredCycles
  DPFilteredCohomologyFiltration DPFirstQuadrantFilteredPages.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredCohomology.
Section Cohomology.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Definition total_cohomology_filtration p n := cohomology_filtration F (Z.of_nat p) n.

Theorem total_cohomology_filtration_image p n (x : cohomology (total_complex K) n) :
    total_cohomology_filtration p n x <-> linear_image (cohomology_map (column_inclusion K p) n) x.
Proof.
split.
- intros [z hz].
  have hf : column_subspace K p n (submodule_val z).
    exact (proj1 (@total_column_filtration_nat R K p n _) (proj1 (submodule_val_mem z))).
  pose w := @submodule_in R (total_term K n) (column_subspace K p n) (submodule_val z) hf.
  have hw : cocycle (column_complex K p) n w.
    apply submodule_val_injective; exact (proj2 (submodule_val_mem z)).
  exists (cohomology_class hw).
  change (cohomology_map (column_inclusion K p) n (cohomology_class hw)=x).
  rewrite -hz /cohomology_class cohomology_map_pi.
  change (quotient_pi (boundaries_in_cycles (total_complex K) n)
    (cycle_map (column_inclusion K p) n (cycle_of_cocycle hw)) =
    quotient_pi (boundaries_in_cycles (total_complex K) n) (filtered_cocycle_to_cycle F (Z.of_nat p) n z)).
  f_equal; apply submodule_val_injective; reflexivity.
- intros [z hz]; have [w hw] := quotient_pi_surjective z.
  have hf : filtered_cocycles F (Z.of_nat p) n (submodule_val (submodule_val w)).
    split.
    + apply (proj2 (@total_column_filtration_nat R K p n _)); exact: submodule_val_mem.
    + have hdz := submodule_val_mem w.
      change (@column_d R K p n (submodule_val w)=0) in hdz.
      have hv := congr1 (fun t : column_term K p n.+1 => submodule_val t) hdz; exact hv.
  exists (@submodule_in R (total_term K n) (filtered_cocycles F (Z.of_nat p) n)
    (submodule_val (submodule_val w)) hf).
  rewrite -hz -hw cohomology_map_pi.
  change (quotient_pi (boundaries_in_cycles (total_complex K) n)
    (filtered_cocycle_to_cycle F (Z.of_nat p) n (@submodule_in R (total_term K n)
      (filtered_cocycles F (Z.of_nat p) n) (submodule_val (submodule_val w)) hf)) =
    quotient_pi (boundaries_in_cycles (total_complex K) n) (cycle_map (column_inclusion K p) n w)).
  f_equal; apply submodule_val_injective; reflexivity.
Qed.

Theorem total_cohomology_filtration_zero_full n (x : cohomology (total_complex K) n) :
    total_cohomology_filtration 0 n x.
Proof.
have [z <-] := quotient_pi_surjective x.
have hz : filtered_cocycles F 0 n (submodule_val z).
  split; [exact (@total_column_filtration_nonpositive R K 0 n (Z.le_refl 0) (submodule_val z))|exact: submodule_val_mem].
exists (@submodule_in R (total_term K n) (filtered_cocycles F 0 n) (submodule_val z) hz).
change (quotient_pi (boundaries_in_cycles (total_complex K) n)
  (filtered_cocycle_to_cycle F 0 n (@submodule_in R (total_term K n) (filtered_cocycles F 0 n) (submodule_val z) hz)) =
  quotient_pi (boundaries_in_cycles (total_complex K) n) z).
f_equal; apply submodule_val_injective; reflexivity.
Qed.

Theorem total_cohomology_filtration_bounded p n (h : (n<p)%coq_nat) (x : cohomology (total_complex K) n) :
    total_cohomology_filtration p n x -> x=0.
Proof.
intros [z <-].
have hz : submodule_val z=0.
  apply: (@total_column_filtration_bounded R K (Z.of_nat p) n _ _ (proj1 (submodule_val_mem z))); lia.
have hz' : z=0 by apply submodule_val_injective; exact hz.
change (filtered_cocycle_class z=0); by rewrite hz' linear0.
Qed.

Theorem total_cohomology_filtration_decreasing p q n (h : (p<=q)%coq_nat) :
    subspace_le (total_cohomology_filtration q n) (total_cohomology_filtration p n).
Proof. apply cohomology_filtration_decreasing; lia. Qed.

End Cohomology.
End DPFirstQuadrantFilteredCohomology.
