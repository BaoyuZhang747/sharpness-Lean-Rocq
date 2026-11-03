From mathcomp Require Import all_ssreflect all_fingroup center.
From DiazPark Require Import FusionMaps FusionSystems FusionQuotientMaps
  FusionQuotientConstruction GroupQuotientInfrastructure.
Import DPFusion DPFusionQuotientConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientNormalization.
Section Normalization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Lemma conjugate_preimages (P Q : {group coset_of Z}) :
  DPFusionSystem.conjugate (system cZ) P Q =
  DPFusionSystem.conjugate F (preimage P) (preimage Q).
Proof.
apply/idP/idP.
- move=> /existsP[b /andP[/existsP[f /andP[Ff hf]] /eqP imQ]].
  apply/existsP; exists f; apply/andP; split=> //; apply/eqP.
  exact: (@lift_onto S F Z cZ P Q f b Ff hf imQ).
- move=> /existsP[f /andP[Ff /eqP imQ]].
  have [b hb] := @exists_descended S F Z cZ P Q f Ff.
  apply/existsP; exists b; apply/andP; split.
  + apply/existsP; exists f; by apply/andP.
  + apply/eqP; apply: val_inj.
    change ((DPFusion.image b : {set coset_of Z}) = Q).
    by rewrite -(@descends_image_quotient S F Z cZ P Q f b hb) imQ cosetpreK.
Qed.

Lemma normalizer_preimage (P : {group coset_of Z}) :
  preimage 'N(P)%G = 'N(preimage P)%G.
Proof.
have h := quotient_normalizer_preimage (DPFusionQuotient.central_normal cZ)
  (kernel_sub_preimage P) (subsetT (preimage P)).
apply: val_inj.
by rewrite !setTI quotientT setTI cosetpreK in h.
Qed.

Lemma normalizer_preimage_card (P : {group coset_of Z}) :
  #|'N(preimage P)| = (#|Z| * #|'N(P)|)%N.
Proof.
have h := congr1 (fun H : {group S} => #|H|) (normalizer_preimage P).
apply: (eq_trans (esym h)).
exact: card_cosetpre.
Qed.

Lemma conjugate_contains_kernel (P Q : {group S}) :
  Z \subset P -> DPFusionSystem.conjugate F P Q -> Z \subset Q.
Proof.
move=> sZP /existsP[f /andP[Ff _]].
have hf := DPFusionQuotient.central_fixes cZ sZP Ff.
apply/subsetP=> z Zz; rewrite -(hf z Zz).
apply: DPFusion.map_into; exact: subsetP sZP z Zz.
Qed.

Lemma preimage_of_quotient (P : {group S}) :
  Z \subset P -> preimage (P / Z)%G = P.
Proof.
move=> sZP.
have nZP := normalS sZP (subsetT P) (DPFusionQuotient.central_normal cZ).
apply: val_inj; by rewrite /preimage /= quotientGK.
Qed.

Lemma fully_normalized_preimage (P : {group coset_of Z}) :
  DPFusionSystem.fully_normalized (system cZ) P =
  DPFusionSystem.fully_normalized F (preimage P).
Proof.
apply/idP/idP.
- move=> /forallP hP; apply/forallP=> Q; apply/implyP=> conjPQ.
  have sZQ := conjugate_contains_kernel (kernel_sub_preimage P) conjPQ.
  have preQ := preimage_of_quotient sZQ.
  have conjbar : DPFusionSystem.conjugate (system cZ) P (Q / Z)%G.
    by rewrite conjugate_preimages preQ.
  have h := implyP (hP (Q / Z)%G) conjbar.
  rewrite -preQ !normalizer_preimage_card.
  exact: leq_mul (leqnn #|Z|) h.
- move=> /forallP hP; apply/forallP=> Q; apply/implyP=> conjPQ.
  have conjpre : DPFusionSystem.conjugate F (preimage P) (preimage Q).
    by rewrite -conjugate_preimages.
  have h := implyP (hP (preimage Q)) conjpre.
  by rewrite !normalizer_preimage_card leq_pmul2l ?cardG_gt0 in h.
Qed.

End Normalization.
End DPFusionQuotientNormalization.
