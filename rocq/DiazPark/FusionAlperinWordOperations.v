From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy FusionSaturationImage
  FusionAlperinWords.
Import DPFusion DPFusionAlperinWords.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAlperinWordOperations.
Section Operations.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma strongly_factorizable_compose P Q R
    (f : DPFusion.map P Q) (g : DPFusion.map Q R) :
  strongly_factorizable F f -> strongly_factorizable F g ->
  strongly_factorizable F (DPFusion.compose f g).
Proof.
move=> hf hg A B d sAP sBR onto hd.
pose f0 := DPFusion.restrict f sAP.
pose i := DPFusion.to_image f0.
have oi : DPFusion.image i = DPFusion.image f0 :=
  DPFusionSaturationImage.image_to_image f0.
pose j := DPFusionConjugacy.onto_inverse oi.
pose k := DPFusion.compose j d.
have hi : factorizable F i.
  apply: (hf A (DPFusion.image f0) i sAP (DPFusion.image_sub f0) oi).
  by move=> x Ax; rewrite /i DPFusion.to_image_in // /f0 DPFusion.restrict_in.
have ok : DPFusion.image k = B.
  exact: DPFusionConjugacy.compose_onto (DPFusionConjugacy.onto_inverse_image oi) onto.
have hk : factorizable F k.
  apply: (hg (DPFusion.image f0) B k (DPFusion.image_sub f0) sBR ok).
  move=> x Ix.
  have Ax : j x \in A := DPFusion.map_into j Ix.
  have Px := subsetP sAP _ Ax.
  have ex : f (j x) = x.
    have e := DPFusionConjugacy.onto_inverse_cancel_right oi Ix.
    change (i (j x) = x) in e.
    by rewrite /i DPFusion.to_image_in // /f0 DPFusion.restrict_in in e.
  by rewrite /k DPFusion.compose_in // (hd _ Ax) DPFusion.compose_in // ex.
have eqd : DPFusion.compose i k = d.
  apply: DPFusion.map_ext=> x Ax.
  have Ix : i x \in DPFusion.image f0 := DPFusion.map_into i Ax.
  rewrite DPFusion.compose_in // /k DPFusion.compose_in //.
  have e := DPFusionConjugacy.onto_inverse_cancel oi Ax.
  change (j (i x) = x) in e; by rewrite e.
rewrite -eqd; exact: factorizable_compose hi hk.
Qed.

Lemma strongly_factorizable_self P Q (f : DPFusion.map P Q) :
  DPFusion.image f = Q -> strongly_factorizable F f -> factorizable F f.
Proof. move=> onto hf; exact: hf P Q f (subxx P) (subxx Q) onto (fun _ _ => erefl). Qed.

End Operations.
End DPFusionAlperinWordOperations.
