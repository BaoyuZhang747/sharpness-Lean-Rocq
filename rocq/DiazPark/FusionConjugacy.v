From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** Conjugacy uses actual onto allowed homomorphisms. Its finite maximizers
    require no saturation axiom and impose no extra structure on the group. *)
Module DPFusionConjugacy.

Section NativeMaps.
Variable S : finGroupType.

Lemma map_image_card (P Q : {group S}) (f : DPFusion.map P Q) :
  #|DPFusion.image f| = #|P|.
Proof.
exact (@card_injm S S P (DPFusion.map_morphism f)
  (DPFusion.map_injm f) P (subxx P)).
Qed.

Lemma identity_image (P : {group S}) :
  DPFusion.image (DPFusion.identity P) = P.
Proof.
apply: val_inj; apply/setP=> x; apply/idP/idP.
- move=> hx; exact: (subsetP (DPFusion.image_sub (DPFusion.identity P)) x hx).
- move=> Px; apply/morphimP; exists x=> //.
  change (x = DPFusion.identity P x).
  by rewrite DPFusion.identity_in.
Qed.

Lemma onto_inverse_domain (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusion.image f = Q -> Q \subset DPFusion.image f.
Proof. by move=> ->. Qed.

Definition onto_inverse (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) : DPFusion.map Q P :=
  DPFusion.restrict (DPFusion.inverse f) (onto_inverse_domain onto).

Lemma onto_inverse_cancel (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) x :
  x \in P -> onto_inverse onto (f x) = x.
Proof.
move=> Px; rewrite /onto_inverse DPFusion.restrict_in ?DPFusion.map_into //.
exact: DPFusion.inverse_cancel.
Qed.

Lemma onto_inverse_cancel_right (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) x :
  x \in Q -> f (onto_inverse onto x) = x.
Proof.
move=> Qx; rewrite /onto_inverse DPFusion.restrict_in //.
apply: DPFusion.inverse_cancel_right; by rewrite onto.
Qed.

Lemma onto_inverse_image (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) :
  DPFusion.image (onto_inverse onto) = P.
Proof.
apply: val_inj; apply/setP=> x; apply/idP/idP.
- move=> hx; exact: (subsetP (DPFusion.image_sub (onto_inverse onto)) x hx).
- move=> Px; have Qfx := DPFusion.map_into f Px.
  apply/morphimP; exists (f x)=> //.
  change (x = onto_inverse onto (f x)).
  by rewrite onto_inverse_cancel.
Qed.

Lemma compose_onto (P Q T : {group S})
    (f : DPFusion.map P Q) (g : DPFusion.map Q T) :
  DPFusion.image f = Q -> DPFusion.image g = T ->
  DPFusion.image (DPFusion.compose f g) = T.
Proof.
move=> ontof ontog; apply: val_inj; apply/setP=> z; apply/idP/idP.
- move=> hz; exact: (subsetP (DPFusion.image_sub (DPFusion.compose f g)) z hz).
- move=> Tz.
  have /morphimP[y Qy _ ->] : z \in DPFusion.image g by rewrite ontog.
  have /morphimP[x Px _ ->] : y \in DPFusion.image f by rewrite ontof.
  apply/morphimP; exists x=> //.
  change (g (f x) = DPFusion.compose f g x).
  by rewrite DPFusion.compose_in.
Qed.

Lemma compose_onto_inverse (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) :
  DPFusion.compose f (onto_inverse onto) = DPFusion.identity P.
Proof.
apply: DPFusion.map_ext=> x Px.
by rewrite DPFusion.compose_in // onto_inverse_cancel // DPFusion.identity_in.
Qed.

Lemma onto_inverse_compose (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) :
  DPFusion.compose (onto_inverse onto) f = DPFusion.identity Q.
Proof.
apply: DPFusion.map_ext=> x Qx.
by rewrite DPFusion.compose_in // onto_inverse_cancel_right // DPFusion.identity_in.
Qed.

End NativeMaps.

Section FusionConjugacy.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma onto_inverse_allowed (P Q : {group S}) (f : DPFusion.map P Q)
    (onto : DPFusion.image f = Q) :
  DPFusionSystem.allowed F f -> DPFusionSystem.allowed F (onto_inverse onto).
Proof.
move=> hf; apply: DPFusionSystem.restriction_allowed.
exact: DPFusionSystem.inverse_closed hf.
Qed.

Lemma conjugate_refl (P : {group S}) : DPFusionSystem.conjugate F P P.
Proof.
apply/existsP; exists (DPFusion.identity P); apply/andP; split.
- exact: DPFusionSystem.identity_allowed.
- by rewrite identity_image.
Qed.

Lemma conjugate_reverse (P Q : {group S}) :
  DPFusionSystem.conjugate F P Q -> DPFusionSystem.conjugate F Q P.
Proof.
move=> /existsP[f /andP[hf /eqP onto]].
apply/existsP; exists (onto_inverse onto); apply/andP; split.
- exact: onto_inverse_allowed hf.
- by rewrite onto_inverse_image.
Qed.

Lemma conjugate_sym (P Q : {group S}) :
  DPFusionSystem.conjugate F P Q = DPFusionSystem.conjugate F Q P.
Proof. apply/idP/idP; exact: conjugate_reverse. Qed.

Lemma conjugate_trans (P Q T : {group S}) :
  DPFusionSystem.conjugate F P Q -> DPFusionSystem.conjugate F Q T ->
  DPFusionSystem.conjugate F P T.
Proof.
move=> /existsP[f /andP[hf /eqP ontof]] /existsP[g /andP[hg /eqP ontog]].
apply/existsP; exists (DPFusion.compose f g); apply/andP; split.
- exact: DPFusionSystem.composition_closed hf hg.
- apply/eqP; exact: compose_onto ontof ontog.
Qed.

Lemma conjugate_card (P Q : {group S}) :
  DPFusionSystem.conjugate F P Q -> #|P| = #|Q|.
Proof.
move=> /existsP[f /andP[_ /eqP <-]].
by rewrite map_image_card.
Qed.

Definition normalized_representative (P : {group S}) : {group S} :=
  arg_max P (DPFusionSystem.conjugate F P) (fun Q => #|'N(Q)|).

Lemma normalized_representative_spec (P : {group S}) :
  DPFusionSystem.conjugate F P (normalized_representative P) /\
  forall Q, DPFusionSystem.conjugate F P Q ->
    (#|'N(Q)| <= #|'N(normalized_representative P)|)%N.
Proof.
rewrite /normalized_representative.
case: arg_maxnP; first exact: conjugate_refl.
by move=> Q hconj hmax; split.
Qed.

Lemma normalized_representative_fully_normalized (P : {group S}) :
  DPFusionSystem.fully_normalized F (normalized_representative P).
Proof.
have [hconj hmax] := normalized_representative_spec P.
apply/forallP=> Q; apply/implyP=> hQ.
apply: hmax; exact: conjugate_trans hconj hQ.
Qed.

Theorem fully_normalized_conjugate_exists (P : {group S}) :
  exists Q, DPFusionSystem.conjugate F P Q /\ DPFusionSystem.fully_normalized F Q.
Proof.
exists (normalized_representative P); split.
- exact: (normalized_representative_spec P).1.
- exact: normalized_representative_fully_normalized.
Qed.

End FusionConjugacy.
End DPFusionConjugacy.
