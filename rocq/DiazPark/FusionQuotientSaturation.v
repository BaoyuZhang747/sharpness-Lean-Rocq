From mathcomp Require Import all_ssreflect all_fingroup center pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization
  FusionQuotientAutomorphisms FusionQuotientExtension FusionReceptivity
  FusionReceptivityCriterion.
Import DPFusion DPFusionQuotientConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientSaturation.
Section Saturation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Lemma quotient_pgroup : p.-group [set: coset_of Z].
Proof.
have h : p.-group ([set: S] / Z) by apply: quotient_pgroup.
by rewrite quotientT in h.
Qed.

Lemma fully_normalized_receptive (Q : {group coset_of Z}) :
  DPFusionSystem.fully_normalized (system cZ) Q ->
  DPFusionReceptivity.receptive (system cZ) Q.
Proof.
move=> hQ P b /existsP[f /andP[Ff hf]] onto.
have pZ : p.-group Z := pgroupS (subsetT Z) pS.
exact: (@DPFusionQuotientExtension.quotient_extension S F Z cZ p pZ sat
  P Q b f Ff hf onto hQ).
Qed.

(** Saturation of the actual full-preimage quotient fusion system, with
    exactly the ordinary finite-p-group, centrality and saturation premises. *)
Theorem central_quotient_saturated : DPFusionSaturation.saturated (system cZ) p.
Proof.
apply: (@DPFusionReceptivityCriterion.saturated_of_normalized_receptive_sylow
  (coset_of Z) (system cZ) p quotient_pgroup).
move=> Q hQ; split.
- exact: fully_normalized_receptive hQ.
- exact: (@DPFusionQuotientAutomorphisms.fully_normalized_sylow S F Z cZ Q p sat hQ).
Qed.

End Saturation.
End DPFusionQuotientSaturation.
