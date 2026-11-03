From mathcomp Require Import all_boot all_algebra all_fingroup center pgroup.
From DiazPark Require Import Category ModuleInfrastructure FusionMaps FusionSystems
  FusionOrbit FusionConjugacy FusionMackeyShape MackeyStructures MackeyPair
  MackeyFusionBridge MackeyFusionMinimal TraceGeneratedRestriction
  FusionQuotientMaps FusionQuotientNormalization FusionQuotientCollectionClosure.
Import DPFusionOrbit DPFusionMackey DPMackeyFusion.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientVanishing.
Section Vanishing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis hM : inclusion_mackey_formula M.
Let full := full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Hypothesis missingZ : ~~ (Z \subset Q).
Variable p : nat.
Hypothesis charp : p%:R = (0 : R).
Hypothesis pS : p.-group [set: S].

Lemma conjugate_missing_center (L : {group S}) :
  DPFusionSystem.conjugate F Q L -> ~~ (Z \subset L).
Proof.
move=> hQL; apply/negP=> sZL.
have sZQ := DPFusionQuotientNormalization.conjugate_contains_kernel cZ sZL
  (DPFusionConjugacy.conjugate_reverse hQL).
by move: missingZ; rewrite sZQ.
Qed.

Lemma minimal_centralizer_noncontained (P L : {group S}) :
  DPFusionSystem.centric F P -> L \subset P ->
  DPFusionSystem.conjugate F Q L -> ~~ (P :&: 'C(L) \subset L).
Proof.
move=> hP sLP hQL; apply/negP=> hcent.
have sZP := DPFusionQuotientCollectionClosure.centric_contains_center cZ hP.
have cZT : Z \subset 'C([set: S]) :=
  subset_trans (DPFusionQuotient.central_sub_center cZ) (subsetIr _ _).
have sZC : Z \subset 'C(L) := centsS (subsetT L) cZT.
have sZI : Z \subset P :&: 'C(L) by rewrite subsetI sZP sZC.
have sZL := subset_trans sZI hcent.
by move: (conjugate_missing_center hQL); rewrite sZL.
Qed.

Theorem centric_value_zero (P : {group S}) :
  DPFusionSystem.centric F P -> forall x : pair_value M P, x = 0.
Proof.
move=> hP x.
apply: (@DPMackeyMinimal.inclusion_restriction_detection S F R full Q leastQ simple P x).
move=> L sLP hQL.
exact: (@DPCentralizerRestriction.centralizer_restriction_zero S F R M hM simple Q
  leastQ L P hQL sLP p charp (pgroupS (subsetT P) pS)
  (minimal_centralizer_noncontained hP sLP hQL) x).
Qed.
End Vanishing.
End DPFusionMackeyQuotientVanishing.

Print Assumptions DPFusionMackeyQuotientVanishing.centric_value_zero.
