From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionSaturationImage FusionCentricCriterion FusionCentricBasics.
Import DPFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentricNormalizerExtension.
Section Extension.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Variable sat : DPFusionSaturation.saturated F p.
Variables U N T : {group S}.
Variable beta : DPFusion.map U T.
Hypothesis beta_allowed : DPFusionSystem.allowed F beta.
Hypothesis centricU : DPFusionSystem.centric F U.
Hypothesis sUN : U \subset N.
Hypothesis sNN : N \subset 'N(U).
Hypothesis compatible : forall n, n \in N ->
  exists t, t \in T /\ {in U, forall x, beta (x ^ n) = (beta x) ^ t}.

Lemma domain_contains_normalizer :
  N \subset DPFusionSaturationImage.intrinsic_extension_domain beta.
Proof.
apply/subsetP=> n Nn; rewrite DPFusionSaturationImage.intrinsic_extension_domainE.
apply/andP; split; first exact: subsetP sNN n Nn.
have [t [_ ht]] := @compatible n Nn.
apply/existsP; exists t; apply/forall_inP=> x Ux; apply/eqP; exact: ht x Ux.
Qed.

Theorem centric_normalizer_extension :
  exists betabar : DPFusion.map N T,
    DPFusionSystem.allowed F betabar /\ {in U, betabar =1 beta}.
Proof.
have cL := DPFusionCentricBasics.centric_image beta_allowed centricU.
have fcL := DPFusionCentricCriterion.centric_fully_centralized cL.
have [bhat [hbhat hext]] := DPFusionSaturationImage.saturated_image_extension sat beta_allowed fcL.
have imageT : DPFusion.image (DPFusion.restrict bhat domain_contains_normalizer) \subset T.
  apply/subsetP=> y /morphimP[n Nn _ ->].
  change (DPFusion.restrict bhat domain_contains_normalizer n \in T).
  rewrite DPFusion.restrict_in //.
  have [t [Tt ht]] := @compatible n Nn.
  have dn : n \in DPFusionSaturationImage.intrinsic_extension_domain beta :=
    subsetP domain_contains_normalizer n Nn.
  have equal_conjugations : {in DPFusion.image beta,
      forall z, z ^ (bhat n) = z ^ t}.
    move=> z /morphimP[x Ux _ hx].
    change (z = beta x) in hx; rewrite hx.
    have Uxn : x ^ n \in U by rewrite memJ_norm ?(subsetP sNN n Nn).
    have dx : x \in DPFusionSaturationImage.intrinsic_extension_domain beta :=
      subsetP domain_contains_normalizer x (subsetP sUN x Ux).
    have hm : bhat (x ^ n) = (bhat x) ^ (bhat n) :=
      morphJ (DPFusion.map_morphism bhat) dx dn.
    rewrite (hext _ Uxn) (hext x Ux) in hm.
    by rewrite -hm; exact: ht x Ux.
  have hratio : bhat n * t^-1 \in 'C(DPFusion.image beta).
    apply/centP=> z Lz; apply/commgP; rewrite commg1_sym.
    apply/conjg_fixP; by rewrite conjgM (equal_conjugations z Lz) conjgK.
  have hratioT : bhat n * t^-1 \in T.
    apply: (subsetP (DPFusion.image_sub beta)).
    exact: (subsetP (DPFusionCentricCriterion.centric_self_centralizing cL) _ hratio).
  have h := groupM hratioT Tt; by rewrite mulgKV in h.
exists (DPFusion.corestrict imageT); split.
- apply: DPFusionSystem.corestriction_allowed.
  exact: DPFusionSystem.restriction_allowed hbhat.
- move=> x Ux; have Nx := subsetP sUN x Ux.
  by rewrite DPFusion.corestrict_in // DPFusion.restrict_in //; exact: hext x Ux.
Qed.

End Extension.
End DPFusionCentricNormalizerExtension.
