(** Full ordinary saturation for the fusion system induced through an
    actual faithful embedding with Sylow image. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionSystems FusionSaturation FusionReceptivityCriterion.
From DiazParkV16b Require Import FiniteGroupFusionEmbedding FiniteGroupFusionEmbeddingImage
  FiniteGroupFusionEmbeddingSubgroups FiniteGroupFusionEmbeddingAutomorphisms
  FiniteGroupFusionEmbeddingExtension.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingSaturation.
Section Saturation.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Variable p : nat.
Hypothesis sylE : p.-Sylow([set: G]) (DPFiniteGroupFusionEmbeddingImage.image_group E).

Theorem saturated : DPFusionSaturation.saturated (DPFiniteGroupFusionEmbedding.system E) p.
Proof.
apply (@DPFusionReceptivityCriterion.saturated_of_normalized_receptive_sylow N
  (DPFiniteGroupFusionEmbedding.system E) p
  (DPFiniteGroupFusionEmbeddingSubgroups.sylow_carrier_pgroup injE sylE)).
move=> P hP; split.
- exact (DPFiniteGroupFusionEmbeddingExtension.fully_normalized_receptive injE sylE hP).
- exact (DPFiniteGroupFusionEmbeddingAutomorphisms.fully_normalized_automizer_sylow injE sylE hP).
Qed.
End Saturation.
End DPFiniteGroupFusionEmbeddingSaturation.

Check DPFiniteGroupFusionEmbeddingSaturation.saturated.
Print Assumptions DPFiniteGroupFusionEmbeddingSaturation.saturated.
