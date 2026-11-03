(** The literal representative map from filtered E1 cycles to cohomology
    of the already constructed native relative column complex. *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex HomologicalCohomology.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalSupport FirstQuadrantCochainSpectralFiltration
  FirstQuadrantCochainSpectralRelative FilteredCochainCycles FilteredCochainPages
  FirstQuadrantFilteredPages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DPFirstQuadrantCochain
  DPFirstQuadrantTotal DPFirstQuadrantSupport DPColumnFiltration DPColumnRelative
  DPFilteredCycles DPFilteredPages DPFirstQuadrantFilteredPages.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredFirstMap.
Section FirstMap.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Lemma first_next_cycles p n x :
    almost_cycles F 0 (Z.succ (Z.of_nat p)) n x <-> column_subspace K p.+1 n x.
Proof.
have he : Z.succ (Z.of_nat p)=Z.of_nat p.+1 by lia.
rewrite he; split.
- intros [hx hdx]; exact (proj1 (@total_column_filtration_nat R K p.+1 n x) hx).
- intro hx; split; [exact (proj2 (@total_column_filtration_nat R K p.+1 n x) hx)|].
  change (filtration F (Z.add (Z.of_nat p.+1) 0) n.+1 (total_d x)).
  rewrite Z.add_0_r; apply filtration_d; exact (proj2 (@total_column_filtration_nat R K p.+1 n x) hx).
Qed.

Definition first_cycle_column p n :
    {linear page_cycle_module F 0 (Z.of_nat p) n -> column_term K p n} :=
  @submodule_map R (total_term K n) (total_term K n) (idfun : {linear _ -> _})
    (almost_cycles F 1 (Z.of_nat p) n) (column_subspace K p n)
    (fun x hx => proj1 (proj1 (@first_cycle_conditions R K p n x) hx)).

Definition first_cycle_relative p n (x : page_cycle_module F 0 (Z.of_nat p) n) : relative_term K p p.+1 n :=
  quotient_pi (relative_subspace K p p.+1 n) (first_cycle_column p n x).

Lemma first_cycle_relative_linear p n : linear (@first_cycle_relative p n).
Proof. intros a x y; by rewrite /first_cycle_relative !linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (page_cycle_module F 0 (Z.of_nat p) n)
  (relative_term K p p.+1 n) _ (@first_cycle_relative p n) (@first_cycle_relative_linear p n).

Lemma first_cycle_relative_cocycle p n x : cocycle (relative_complex K p p.+1) n (first_cycle_relative x).
Proof.
change (@relative_d R K p p.+1 n (quotient_pi (relative_subspace K p p.+1 n) (first_cycle_column p n x))=0).
rewrite relative_d_pi quotient_pi_kernel.
exact (proj2 (proj1 (@first_cycle_conditions R K p n (submodule_val x)) (submodule_val_mem x))).
Qed.

Definition first_cycle_native p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    cycle_module (relative_complex K p p.+1) n := cycle_of_cocycle (first_cycle_relative_cocycle x).

Lemma first_cycle_native_linear p n : linear (@first_cycle_native p n).
Proof. intros a x y; apply submodule_val_injective; exact: linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (page_cycle_module F 0 (Z.of_nat p) n)
  (cycle_module (relative_complex K p p.+1) n) _ (@first_cycle_native p n) (@first_cycle_native_linear p n).

Definition first_cycle_native_class p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    cohomology (relative_complex K p p.+1) n :=
  quotient_pi (boundaries_in_cycles (relative_complex K p p.+1) n) (first_cycle_native x).

Lemma first_cycle_native_class_linear p n : linear (@first_cycle_native_class p n).
Proof. intros a x y; by rewrite /first_cycle_native_class !linearP. Qed.
HB.instance Definition _ p n := GRing.isLinear.Build R (page_cycle_module F 0 (Z.of_nat p) n)
  (cohomology (relative_complex K p p.+1) n) _ (@first_cycle_native_class p n) (@first_cycle_native_class_linear p n).

Lemma first_cycle_native_surjective p n (y : cohomology (relative_complex K p p.+1) n) :
    exists x, first_cycle_native_class x=y.
Proof.
have [z <-] := quotient_pi_surjective y.
have [w hw] := quotient_pi_surjective (submodule_val z).
have hd : column_subspace K p.+1 n.+1 (total_d (submodule_val w)).
  have hz := submodule_val_mem z.
  change (@relative_d R K p p.+1 n (submodule_val z)=0) in hz.
  rewrite -hw relative_d_pi quotient_pi_kernel in hz; exact hz.
have hx : almost_cycles F 1 (Z.of_nat p) n (submodule_val w).
  apply (proj2 (@first_cycle_conditions R K p n (submodule_val w))); split; [exact: submodule_val_mem|exact hd].
exists (@submodule_in R (total_term K n) (almost_cycles F 1 (Z.of_nat p) n) (submodule_val w) hx).
unfold first_cycle_native_class; f_equal; apply submodule_val_injective.
change (quotient_pi (relative_subspace K p p.+1 n) (first_cycle_column p n
  (@submodule_in R (total_term K n) (almost_cycles F 1 (Z.of_nat p) n) (submodule_val w) hx)) = submodule_val z).
rewrite -hw; f_equal; apply submodule_val_injective; reflexivity.
Qed.

End FirstMap.
End DPFirstQuadrantFilteredFirstMap.
