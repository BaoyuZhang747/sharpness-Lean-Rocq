From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionSaturationImage
  FusionAutomorphisms GroupKNormalizer FusionCentralizerMaps FusionCentralizer
  FusionCentralizerAut FusionCentralizerReceptive FusionCentralizerCompression
  FusionCentralizerTransport FusionCentralizerNormalizedImage.
Import DPFusion DPFusionSubgroup DPFusionCentralizer DPFusionAutomorphisms
  DPFusionCentralizerCompression DPFusionCentralizerTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerNormalized.
Section Normalized.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Hypothesis abE : abelian E.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Hypothesis hE : DPFusionSystem.fully_centralized F E.
Local Notation T := [subg 'C(E)%G]%type.
Variable P : {group T}.
Hypothesis hP : DPFusionSystem.fully_normalized (system F E) P.

Lemma fully_normalized_transport_card (B : {group S})
    (theta : DPFusion.map (joint P) B) :
  DPFusionSystem.allowed F theta -> DPFusion.image theta = B ->
  (#|transported_normalizer F theta| <= #|'N(P)|)%N.
Proof.
move=> htheta onto.
have [g [hg gfix]] := inverse_E_centralizer_extension abE sat hE htheta onto.
pose f := DPFusionCentralizerNormalizedImage.local_map abE onto g.
have hf : DPFusionSystem.allowed (system F E) f :=
  DPFusionCentralizerNormalizedImage.local_map_allowed abE htheta onto hg gfix.
have conjP : DPFusionSystem.conjugate (system F E) P (DPFusion.image f).
  apply/existsP; exists (DPFusion.to_image f); apply/andP; split.
  - exact: DPFusionSystem.image_closed hf.
  - apply/eqP; exact: DPFusionSaturationImage.image_to_image.
have hN := implyP (forallP hP (DPFusion.image f)) conjP.
exact: leq_trans (DPFusionCentralizerNormalizedImage.transported_normalizer_card F abE onto g) hN.
Qed.

End Normalized.
End DPFusionCentralizerNormalized.
