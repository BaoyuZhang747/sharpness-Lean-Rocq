(** E3 comparison through the accepted v2.9 Corollary 1.2.  The actual Ran,
    cover and native coefficient constructions are reused unchanged; their
    positive acyclicity is proved anew through the new manuscript route. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup abelian zmodp boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryIsomorphism CategoryModules CategoryModuleExactness CategoryModuleRightKan
  CategoryDerivedLimits CategoryDerivedIsomorphism CategoryFibration HomologicalModuleIso
  FusionSystems FusionSaturation FusionOrbit FusionCentralizer FusionCentralizerSaturation
  FusionCentralizerCoverProjection FusionCentralizerDetectionCover.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient.
From DiazParkV28 Require Import CategoryFiberRanComparison FusionCentralizerComma RightKanCohomology.
From DiazParkV29 Require Import MainCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFusionOrbit
  DPFusionCentralizerCoverProjection DPGroupCohomologyOrbitCoefficient.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOE3.
Section Cohomology.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable n : nat.
Local Notation K := [the fieldType of 'F_p].
Local Notation A := [the lmodType K of K^o].
Local Notation tau := (DPV28CentralizerComma.tau F p).
Local Notation ambient := (@DPV28RightKanCohomology.ambient_cohomology S F p n).
Local Notation cover := (@DPV28RightKanCohomology.cover_cohomology S F p n).
Local Notation ran := (@DPV28RightKanCohomology.ran_cohomology S F p n).
Local Notation Hn := (@DPV28RightKanCohomology.H_n S F p n).
Local Notation restriction := (@DPV28RightKanCohomology.centralizer_restriction S F p pS sat n).
Local Notation fibre := (@DPV28RightKanCohomology.fibre_cohomology S F p n).

Lemma centralizer_positive_limits_zero (B : elementary_object F p) (j : nat) :
  forall v : derived_limit K (restriction B) j.+1, v = 0.
Proof.
have /and3P[ntE elE fcE] := valP B.
have abE : abelian (val B) := abelem_abelian elE.
have pC := @DPFusionCentralizerSaturation.centralizer_pgroup S (val B) p pS.
have satC := @DPFusionCentralizerSaturation.centralizer_saturated S F (val B) abE p pS sat fcE.
pose e := functor_iso (derived_limit_functor K _ j.+1)
  (iso_symm (@DPV28RightKanCohomology.centralizer_coefficient_nat_iso S F p pS sat n B)).
intro v; apply (@module_iso_hom_injective K _ _ e).
rewrite module_hom_zero.
exact (@DPV29GroupCohomologySharpness.prime_field_higher_limits_zero _
  (DPFusionCentralizer.system F (val B)) p hp pC satC A n j _).
Qed.

Lemma fibre_positive_limits_zero (B : elementary_object F p) (j : nat) :
  forall v : derived_limit K (fibre B) j.+1, v = 0.
Proof.
pose e := nat_iso_component (derived_category_iso_nat_iso K
  (@DPV28CentralizerComma.centralizer_fiber_iso S F p sat pS B) j.+1) (fibre B).
have ht : forall v : derived_limit K
  (functor_comp (category_iso_forward (@DPV28CentralizerComma.centralizer_fiber_iso S F p sat pS B))
    (fibre B)) j.+1, v = 0.
  rewrite DPV28RightKanCohomology.centralizer_fibre_coefficient.
  exact: centralizer_positive_limits_zero.
intro v; apply (@module_iso_hom_injective K _ _ e).
rewrite module_hom_zero; exact: ht.
Qed.

Hypothesis ntS : [set: S] :!=: 1%G.

(** Includes degree zero; only positive fibre acyclicity is required. *)
Definition higher_limit_comparison (s : nat) :
  @isomorphism (module_category K) (derived_limit K Hn s)
    (derived_limit K ambient s) :=
  module_iso_comp
    (iso_symm (nat_iso_component (derived_category_iso_nat_iso K
      (DPV28FiberRanComparison.double_opposite_iso (elementary_category F p)) s) ran))
    (module_iso_comp
      (@DPV28FiberRanComparison.fibre_acyclic_higher_limit_iso K _ _ tau
        (@DPV28CentralizerComma.tau_fibration S F p sat) cover fibre_positive_limits_zero s)
      (iso_symm (@DPFusionCentralizerDetectionCover.centralizer_cover_derived_iso
        S F p pS ntS sat K ambient s))).

Theorem successor_higher_limits_zero (j : nat) :
  forall v : derived_limit K Hn j.+1, v = 0.
Proof.
intro v; apply (@module_iso_hom_injective K _ _ (higher_limit_comparison j.+1)).
rewrite module_hom_zero.
exact (@DPV29GroupCohomologySharpness.prime_field_higher_limits_zero S F p hp pS sat A n j _).
Qed.

Theorem positive_higher_limits_zero (s : nat) :
  (0 < s)%N -> forall v : derived_limit K Hn s, v = 0.
Proof. case: s => [|j] // _; exact: successor_higher_limits_zero. Qed.

End Cohomology.
End DPBLOE3.
