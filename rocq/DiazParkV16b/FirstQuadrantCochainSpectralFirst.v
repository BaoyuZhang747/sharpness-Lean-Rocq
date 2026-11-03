(** The first exact couple and first differential of the actual column
    filtration. The second index is total cochain degree: d1 raises both
    indices by one. In (p,q) indexing this is bidegree (1,0). *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalConnecting.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex
  FirstQuadrantCochainSpectralFiltration FirstQuadrantCochainSpectralRelative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalConnecting DPFirstQuadrantCochain DPColumnFiltration DPColumnRelative.
Local Open Scope ring_scope.

Module DPColumnFirstPage.
Section FirstPage.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition filtered_cohomology p n : lmodType R := cohomology (column_complex K p) n.
Definition first_page p n : lmodType R := cohomology (relative_complex K p p.+1) n.

Definition filtration_succ p : (p <= p.+1)%coq_nat := Nat.le_succ_diag_r p.

Definition couple_i p n : {linear filtered_cohomology p.+1 n -> filtered_cohomology p n} :=
  cohomology_map (column_transition K (filtration_succ p)) n.

Definition couple_j p n : {linear filtered_cohomology p n -> first_page p n} :=
  cohomology_map (relative_projection K p p.+1) n.

Definition couple_k p n : {linear first_page p n -> filtered_cohomology p.+1 n.+1} :=
  relative_connecting K (filtration_succ p) n.

Theorem couple_exact p n :
    linear_exact (couple_i p n) (couple_j p n) /\
    linear_exact (couple_j p n) (couple_k p n) /\
    linear_exact (couple_k p n) (couple_i p n.+1).
Proof. exact: (proj2 (relative_cohomology_exact K (filtration_succ p)) n). Qed.

Theorem couple_i_zero_injective p : injective (couple_i p 0%N).
Proof. exact: (proj1 (relative_cohomology_exact K (filtration_succ p))). Qed.

Definition first_d p n (x : first_page p n) : first_page p.+1 n.+1 :=
  couple_j p.+1 n.+1 (couple_k p n x).

Lemma first_d_linear p n : linear (@first_d p n).
Proof. intros a x y; by rewrite /first_d !linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (first_page p n) (first_page p.+1 n.+1)
  _ (@first_d p n) (@first_d_linear p n).

Theorem first_d_squared p n (x : first_page p n) : first_d (first_d x) = 0.
Proof.
change (couple_j p.+2 n.+2 (couple_k p.+1 n.+1 (couple_j p.+1 n.+1 (couple_k p n x))) = 0).
have hz := linear_exact_composite_zero (proj1 (proj2 (couple_exact p.+1 n.+1))) (couple_k p n x).
by rewrite hz linear0.
Qed.

Theorem first_page_below_column_zero p n (h : (n < p)%coq_nat) (x : first_page p n) : x = 0.
Proof.
have [z <-] := quotient_pi_surjective x.
have hz : z = 0.
  apply submodule_val_injective.
  have [v hv] := quotient_pi_surjective (submodule_val z).
  have vz : v = 0 := column_beyond_degree_zero h v.
  by rewrite -hv vz linear0.
by rewrite hz linear0.
Qed.

End FirstPage.
End DPColumnFirstPage.
