(** The proved filtered-cycle pages of the actual finite-diagonal total complex.
    The integer filtration is full in nonpositive columns, not artificially zero. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalSupport FirstQuadrantCochainSpectralFiltration
  FirstQuadrantCochainIntegerNative FilteredCochainCycles FilteredCochainPages
  FilteredCochainPageHomology FilteredCochainPageIteration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFirstQuadrantCochain DPFirstQuadrantTotal
  DPFirstQuadrantSupport DPColumnFiltration DPIntegerNative DPFilteredCycles DPFilteredPages
  DPFilteredPageHomology DPFilteredPageIteration.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredPages.
Section Pages.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition total_column_filtration : cochain_filtration (total_complex K).
Proof.
refine (@CochainFiltration R (total_complex K) (fun p n => column_subspace K (Z.to_nat p) n) _ _).
- intros p q n hpq; exact (@column_subspace_decreasing R K (Z.to_nat p) (Z.to_nat q) n (integer_to_nat_mono hpq)).
- intros p n x hx; exact: total_d_supported hx.
Defined.

Lemma total_column_filtration_nat p n x :
    filtration total_column_filtration (Z.of_nat p) n x <-> column_subspace K p n x.
Proof. change (column_subspace K (Z.to_nat (Z.of_nat p)) n x <-> column_subspace K p n x); by rewrite Nat2Z.id. Qed.

Lemma total_column_filtration_nonpositive p n (h : Z.le p 0) x :
    filtration total_column_filtration p n x.
Proof.
change (column_subspace K (Z.to_nat p) n x).
have hp : Z.to_nat p=0%N by destruct p; simpl; lia.
rewrite hp; exact: column_zero_full.
Qed.

Lemma total_column_filtration_bounded p n (h : Z.lt (Z.of_nat n) p) x :
    filtration total_column_filtration p n x -> x=0.
Proof.
intro hx; apply supported_past_diagonal_zero.
have hp : (n.+1 <= Z.to_nat p)%coq_nat.
  have hn : Z.le 0 (Z.of_nat n.+1) by lia.
  have hp : Z.le 0 p by lia.
  have hle : Z.le (Z.of_nat n.+1) p by lia.
  have hnat := proj1 (Z2Nat.inj_le _ _ hn hp) hle; by rewrite Nat2Z.id in hnat.
exact: supported_from_mono hx hp.
Qed.

Definition total_filtered_page r p n := page total_column_filtration r p n.
Definition total_filtered_d r p n := page_d total_column_filtration r p n.
Definition total_filtered_next_homology_iso r p n := next_page_homology_iso total_column_filtration r p n.

Lemma first_cycle_conditions p n x :
    almost_cycles total_column_filtration 1 (Z.of_nat p) n x <->
      column_subspace K p n x /\ column_subspace K p.+1 n.+1 (total_d x).
Proof.
change (column_subspace K (Z.to_nat (Z.of_nat p)) n x /\
  column_subspace K (Z.to_nat (Z.add (Z.of_nat p) (Z.of_nat 1))) n.+1 (total_d x) <->
    column_subspace K p n x /\ column_subspace K p.+1 n.+1 (total_d x)).
have he : Z.add (Z.of_nat p) (Z.of_nat 1)=Z.of_nat p.+1 by lia.
by rewrite he !Nat2Z.id.
Qed.

End Pages.
End DPFirstQuadrantFilteredPages.
