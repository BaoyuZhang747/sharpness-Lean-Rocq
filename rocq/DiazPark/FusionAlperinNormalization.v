From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy
  FusionSaturationImage FusionNormalizerExtension FusionAlperinWords
  FusionAlperinWordOperations FusionAlperinGrowth.
Import DPFusion DPFusionAlperinWords DPFusionConjugacy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAlperinNormalization.
Section Normalization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable P : {group S}.
Hypothesis hP : P \proper [set: S].
Hypothesis hbig : forall (A B : {group S}) (d : DPFusion.map A B),
  DPFusionSystem.allowed F d -> DPFusion.image d = B ->
  (#|P| < #|A|)%N -> strongly_factorizable F d.

Theorem normalizing_words (A R : {group S}) (d : DPFusion.map A R) :
  #|A| = #|P| -> DPFusionSystem.allowed F d -> DPFusion.image d = R ->
  DPFusionSystem.fully_normalized F R ->
  exists psi : DPFusion.map A R,
    DPFusionSystem.allowed F psi /\
    exists onto : DPFusion.image psi = R,
      strongly_factorizable F psi /\ strongly_factorizable F (onto_inverse onto).
Proof.
move=> hAP hd onto hR.
have hA : A \proper [set: S].
  rewrite properEcard subsetT hAP /=; exact: proper_card hP.
have hlarge : (#|P| < #|'N(A)|)%N.
  rewrite -hAP; exact: DPFusionAlperinGrowth.normalizer_card_growth pS hA.
have [psi [hpsi [opsi [h [hh hext]]]]] :=
  DPFusionNormalizerExtension.normalizer_extension pS sat hd onto hR.
pose i := DPFusion.to_image h.
have oi : DPFusion.image i = DPFusion.image h := DPFusionSaturationImage.image_to_image h.
have hi : DPFusionSystem.allowed F i := DPFusionSystem.image_closed hh.
have hRi : R \subset DPFusion.image h.
  apply/subsetP=> r Rr.
  have /morphimP[x Ax _ ex] : r \in DPFusion.image psi by rewrite opsi.
  rewrite ex DPFusion.map_morphismE -(hext x Ax).
  exact: DPFusion.image_mem (subsetP (normG A) x Ax).
have hlargeI : (#|P| < #|DPFusion.image h|)%N.
  by rewrite map_image_card.
have gen_i : strongly_factorizable F i := @hbig _ _ i hi oi hlarge.
have gen_j : strongly_factorizable F (onto_inverse oi).
  exact: (@hbig _ _ (onto_inverse oi) (onto_inverse_allowed oi hi)
    (onto_inverse_image oi) hlargeI).
exists psi; split=> //; exists opsi; split.
- apply: (strongly_factorizable_restrict gen_i (normG A) hRi).
  move=> x Ax; rewrite /i DPFusion.to_image_in ?(subsetP (normG A) x Ax) //.
  exact: esym (hext x Ax).
- apply: (strongly_factorizable_restrict gen_j hRi (normG A)).
  move=> r Rr.
  have Ar : onto_inverse opsi r \in A := DPFusion.map_into (onto_inverse opsi) Rr.
  have Nr := subsetP (normG A) _ Ar.
  have Ir := subsetP hRi r Rr.
  have Nj := DPFusion.map_into (onto_inverse oi) Ir.
  apply: (DPFusion.map_injective (f := i) Nr Nj).
  rewrite (onto_inverse_cancel_right oi Ir) /i DPFusion.to_image_in // hext //.
  exact: (onto_inverse_cancel_right opsi Rr).
Qed.

End Normalization.
End DPFusionAlperinNormalization.


