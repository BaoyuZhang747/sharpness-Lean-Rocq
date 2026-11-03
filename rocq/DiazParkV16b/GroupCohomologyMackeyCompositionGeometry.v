(** Actual inverse-image geometry used to compare transfers in a composite
    fusion injection. Every subgroup and inverse is the existing literal one. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionConjugacy
  FusionMackeyShape FusionCentricSpanNormalization FusionSaturationImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion.
Local Open Scope group_scope.

Module DPGroupCohomologyMackeyCompositionGeometry.
Section Composition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T : {group S}.
Variable f : DPFusionSystem.arrow F P Q.
Variable g : DPFusionSystem.arrow F Q T.
Local Notation fg := (DPFusionSystem.arrow_compose f g).
Local Notation I := (DPFusion.image (val f)).
Local Notation J := (DPFusion.image (val g)).
Local Notation K := (DPFusion.image (val fg)).

Lemma composite_image_sub_image : K \subset J.
Proof. exact: DPFusionCentricSpanNormalization.composite_image_sub. Qed.

Definition inverse_composite_image : DPFusionSystem.arrow F K I :=
  DPFusionSystem.arrow_compose (DPFusionMackey.inverse_arrow fg)
    (DPFusionMackey.image_arrow f).

Lemma inverse_composite_image_value x (hx : x \in K) :
  DPFusion.map_fun (val inverse_composite_image) x = DPFusion.inverse (val g) x.
Proof.
have hxJ := subsetP composite_image_sub_image x hx.
have hy : DPFusion.inverse (val fg) x \in P := DPFusion.map_into _ hx.
have hz : DPFusion.map_fun (val f) (DPFusion.inverse (val fg) x) \in Q :=
  DPFusion.map_into _ hy.
have he := @DPFusion.inverse_cancel_right S P T (val fg) x hx.
change (DPFusion.compose (val f) (val g) (DPFusion.inverse (val fg) x) = x) in he.
rewrite DPFusion.compose_in // in he.
change (DPFusion.compose (DPFusion.inverse (val fg)) (DPFusion.to_image (val f)) x =
  DPFusion.inverse (val g) x).
rewrite DPFusion.compose_in // DPFusion.to_image_in //.
rewrite -{2}he; symmetry; exact: DPFusion.inverse_cancel.
Qed.

Lemma inverse_composite_factorization :
  DPFusionSystem.arrow_compose inverse_composite_image (DPFusionMackey.inverse_arrow f) =
    DPFusionMackey.inverse_arrow fg.
Proof.
apply val_inj.
transitivity (DPFusion.compose (DPFusion.inverse (val fg))
  (DPFusion.compose (DPFusion.to_image (val f)) (DPFusion.inverse (val f)))).
- exact: DPFusion.compose_assoc.
- rewrite DPFusion.to_image_inverse; exact: DPFusion.compose_identity.
Qed.

Lemma inverse_image_on_composite :
  (DPFusion.map_morphism (DPFusion.inverse (val g)) @* K)%G = I.
Proof.
apply val_inj; apply/eqP; rewrite eqEcard.
apply/andP; split.
- apply/subsetP => y /morphimP[x hxJ hxK ->].
  change (DPFusion.inverse (val g) x \in I).
  rewrite -(inverse_composite_image_value hxK).
  exact: DPFusion.map_into hxK.
- rewrite (@card_injm S S J (DPFusion.map_morphism (DPFusion.inverse (val g)))
    (DPFusion.map_injm (DPFusion.inverse (val g))) K composite_image_sub_image).
  change (#|I| <= #|K|)%N.
  by rewrite !DPFusionConjugacy.map_image_card leqnn.
Qed.

Lemma inverse_image_on_image :
  (DPFusion.map_morphism (DPFusion.inverse (val g)) @* J)%G = Q.
Proof.
change (DPFusion.image (DPFusion.inverse (val g)) = Q).
apply val_inj; apply/eqP; rewrite eqEcard DPFusion.image_sub.
by rewrite !DPFusionConjugacy.map_image_card leqnn.
Qed.

End Composition.
End DPGroupCohomologyMackeyCompositionGeometry.

