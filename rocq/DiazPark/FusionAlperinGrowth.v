From mathcomp Require Import all_ssreflect all_fingroup pgroup nilpotent sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionAutomorphisms FusionCentricCriterion.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAlperinGrowth.
Section GroupGrowth.
Variable S : finGroupType.

Lemma proper_normalizer_growth (p : nat) (P : {group S}) :
  p.-group [set: S] -> P \proper [set: S] -> P \proper 'N(P).
Proof.
move=> pS hP.
have h := nilpotent_proper_norm (pgroup_nil pS) hP.
by rewrite setTI in h.
Qed.

Lemma normalizer_card_growth (p : nat) (P : {group S}) :
  p.-group [set: S] -> P \proper [set: S] -> (#|P| < #|'N(P)|)%N.
Proof. move=> pS hP; exact: proper_card (proper_normalizer_growth pS hP). Qed.

Lemma nonselfcentralizing_extension_domain_proper (P Q : {group S})
    (f : DPFusion.map P Q) :
  ~~ ('C(P) \subset P) -> P \proper DPFusionSaturation.extension_domain f.
Proof.
move=> hC; rewrite properE DPFusionSaturation.source_extension_domain /=.
apply/negP=> sNP.
have sCP := subset_trans (DPFusionSaturation.centralizer_extension_domain f) sNP.
by move: hC; rewrite sCP.
Qed.

End GroupGrowth.

Section Extension.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable P : {group S}.
Variable a : DPFusion.map P P.

Lemma nonselfcentralizing_automorphism_extension :
  DPFusionSystem.allowed F a -> DPFusionSystem.fully_centralized F P ->
  ~~ ('C(P) \subset P) ->
  exists (Q : {group S}) (fhat : DPFusion.map Q [set: S]%G),
    P \proper Q /\ DPFusionSystem.allowed F fhat /\ {in P, fhat =1 a}.
Proof.
move=> ha hP hC.
have [fhat [hh he]] := @DPFusionSaturation.saturation_extension S F p sat
  P P a ha (DPFusionAutomorphisms.endomorphism_image a) hP.
exists (DPFusionSaturation.extension_domain a), fhat; split.
- exact: nonselfcentralizing_extension_domain_proper hC.
- by split.
Qed.

Theorem noncentric_automorphism_extension :
  DPFusionSystem.allowed F a -> DPFusionSystem.fully_centralized F P ->
  ~~ DPFusionSystem.centric F P ->
  exists (Q : {group S}) (fhat : DPFusion.map Q [set: S]%G),
    P \proper Q /\ DPFusionSystem.allowed F fhat /\ {in P, fhat =1 a}.
Proof.
move=> ha hP hn.
have hC : ~~ ('C(P) \subset P).
  apply/negP=> sCP.
  have hc : DPFusionSystem.centric F P.
    apply: (proj2 (@DPFusionCentricCriterion.saturated_centric_iff S F p sat P)).
    by split.
  by move: hn; rewrite hc.
exact: nonselfcentralizing_automorphism_extension ha hP hC.
Qed.

End Extension.
End DPFusionAlperinGrowth.

Print Assumptions DPFusionAlperinGrowth.proper_normalizer_growth.
Print Assumptions DPFusionAlperinGrowth.normalizer_card_growth.
Print Assumptions DPFusionAlperinGrowth.nonselfcentralizing_extension_domain_proper.
Print Assumptions DPFusionAlperinGrowth.nonselfcentralizing_automorphism_extension.
Print Assumptions DPFusionAlperinGrowth.noncentric_automorphism_extension.
