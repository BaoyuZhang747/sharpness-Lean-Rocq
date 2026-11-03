(** Actual Sylow normalizers for fusion through a faithful embedding. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import FiniteGroupFusionEmbedding
  FiniteGroupFusionEmbeddingImage FiniteGroupFusionEmbeddingSubgroups FiniteGroupFusionNormalizer.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFiniteGroupFusionEmbeddingImage DPFiniteGroupFusionEmbeddingSubgroups.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingNormalizer.
Section Normalizer.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.

Theorem fully_normalized_normalizer_sylow p
    (sylE : p.-Sylow([set: G]) (image_group E)) (P : {group N}) :
    DPFusionSystem.fully_normalized (DPFiniteGroupFusionEmbedding.system E) P ->
    p.-Sylow('N(ambient E P)) 'N_(image_group E)(ambient E P).
Proof.
move=> hP.
apply: (DPFiniteGroupFusionNormalizer.sylow_normalizer_of_max sylE (ambient_sub E P)).
move=> g hg.
have hconj := conjugate_from injE hg.
have hc := implyP (forallP hP (from_ambient E (ambient E P :^ g)%G)) hconj.
rewrite -!(ambient_card injE) !(ambient_normalizer injE) (ambient_from hg) in hc.
exact hc.
Qed.
End Normalizer.
End DPFiniteGroupFusionEmbeddingNormalizer.

Print Assumptions DPFiniteGroupFusionEmbeddingNormalizer.fully_normalized_normalizer_sylow.
