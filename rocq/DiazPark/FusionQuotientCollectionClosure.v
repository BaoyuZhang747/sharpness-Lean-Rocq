From mathcomp Require Import all_ssreflect all_fingroup center pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy
  FusionCentricBasics FusionCentricCriterion FusionQuotientMaps
  FusionQuotientConstruction FusionQuotientNormalization FusionQuotientCollection.
Import DPFusionQuotientConstruction DPFusionQuotientNormalization
  DPFusionQuotientCollection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientCollectionClosure.
Section Closure.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Theorem collection_conjugate (P Q : {group S}) :
  DPFusionSystem.conjugate F P Q -> collection cZ P -> collection cZ Q.
Proof.
move=> hPQ /andP[sZP hP].
have sZQ := conjugate_contains_kernel cZ sZP hPQ.
rewrite /collection sZQ /=.
apply: DPFusionCentricBasics.centric_conjugate _ hP.
by rewrite conjugate_preimages (preimage_of_quotient cZ sZP)
  (preimage_of_quotient cZ sZQ).
Qed.

Theorem collection_overgroup (P Q : {group S}) :
  P \subset Q -> collection cZ P -> collection cZ Q.
Proof.
move=> sPQ /andP[sZP hP].
rewrite /collection (subset_trans sZP sPQ) /=.
apply: (@DPFusionCentricBasics.centric_overgroup _ (system cZ) (P / Z)%G (Q / Z)%G _ hP).
exact: quotientS.
Qed.

Theorem centric_contains_center (P : {group S}) :
  DPFusionSystem.centric F P -> Z \subset P.
Proof.
move=> hP.
have cZT : Z \subset 'C([set: S]) :=
  subset_trans (DPFusionQuotient.central_sub_center cZ) (subsetIr _ _).
exact: subset_trans (centsS (subsetT P) cZT)
  (DPFusionCentricCriterion.centric_self_centralizing hP).
Qed.
End Closure.
End DPFusionQuotientCollectionClosure.

Print Assumptions DPFusionQuotientCollectionClosure.collection_conjugate.
Print Assumptions DPFusionQuotientCollectionClosure.collection_overgroup.
