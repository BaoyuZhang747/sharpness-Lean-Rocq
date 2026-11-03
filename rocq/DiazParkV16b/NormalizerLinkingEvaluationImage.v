(** The image factorization of an actual linking arrow, with its prescribed
    inclusion and its literal projection. No choice of an unrelated lift is used. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionCentricBasics FusionSaturationImage.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFactorization
  LinkingSystemIsomorphisms.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingFactorization DPLinkingIsomorphisms.
Local Open Scope group_scope.

Module DPNormalizerLinkingEvaluationImage.
Section Image.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).
Variables P Q : Obj.
Variable f : linking_hom L P Q.

Definition image_object : Obj :=
  Sub (DPFusion.image (val (linking_projection L f)))
    (DPFusionCentricBasics.centric_image (valP (linking_projection L f)) (valP P)).

Definition image_sub : val image_object \subset val Q :=
  DPFusion.image_sub (val (linking_projection L f)).

Definition image_arrow : DPFusionSystem.arrow F (val P) (val image_object) :=
  Sub (DPFusion.to_image (val (linking_projection L f)))
    (DPFusionSystem.image_closed (valP (linking_projection L f))).

Lemma image_triangle :
    DPFusionSystem.arrow_compose image_arrow
      (linking_projection L (inclusion L image_sub)) = linking_projection L f.
Proof.
apply val_inj; change (DPFusion.compose (val image_arrow)
  (val (linking_projection L (inclusion L image_sub))) = val (linking_projection L f)).
rewrite projection_inclusion; exact: DPFusion.image_factorization.
Qed.

Definition image_factor : linking_hom L P image_object := factorization image_triangle.

Lemma image_factor_projection : linking_projection L image_factor = image_arrow.
Proof. exact: factorization_projection. Qed.

Lemma image_factor_inclusion : linking_compose L image_factor (inclusion L image_sub) = f.
Proof. exact: factorization_commutes. Qed.

Lemma image_factor_surjective : DPFusion.image (val (linking_projection L image_factor)) =
    val image_object.
Proof. rewrite image_factor_projection; exact: DPFusionSaturationImage.image_to_image. Qed.

Definition image_isomorphism : @isomorphism (linking_category L) P image_object :=
  isomorphism_of_image_eq image_factor_surjective.

Lemma image_isomorphism_hom : iso_hom image_isomorphism = image_factor.
Proof. reflexivity. Qed.

Lemma image_isomorphism_inclusion :
    @compose (linking_category L) P image_object Q
      (iso_hom image_isomorphism) (inclusion L image_sub) = f.
Proof. exact: image_factor_inclusion. Qed.

Lemma image_card : #|val image_object| = #|val P|.
Proof.
rewrite /image_object /= /DPFusion.image /= morphimEdom.
exact: card_in_imset (@DPFusion.map_injective S (val P) (val Q) (val (linking_projection L f))).
Qed.

Lemma image_eq_of_card (h : #|val P| = #|val Q|) : val image_object = val Q.
Proof.
apply: val_inj; apply/eqP; rewrite eqEcard; apply/andP; split; first exact image_sub.
by rewrite image_card h.
Qed.

Definition isomorphism_of_card (h : #|val P| = #|val Q|) :
    @isomorphism (linking_category L) P Q :=
  isomorphism_of_image_eq (image_eq_of_card h).

Lemma isomorphism_of_card_hom (h : #|val P| = #|val Q|) :
    iso_hom (isomorphism_of_card h) = f.
Proof. reflexivity. Qed.
End Image.
End DPNormalizerLinkingEvaluationImage.
