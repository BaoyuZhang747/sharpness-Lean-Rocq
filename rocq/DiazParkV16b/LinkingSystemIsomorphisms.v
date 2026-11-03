(** Actual linking isomorphisms lifting raw fusion isomorphisms.  A
    right inverse to the projected map lifts by the unique triangle
    factorization; monicity makes it a two-sided inverse. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemFinite LinkingSystemCancellation LinkingSystemFactorization
  LinkingSystemAutomorphisms.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingFinite
  DPLinkingCancellation DPLinkingFactorization.
Local Open Scope group_scope.

Module DPLinkingIsomorphisms.
Section Isomorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Section ProjectedRetraction.
Variables P Q : Obj.
Variable f : linking_hom L P Q.
Variable b : DPFusionSystem.arrow F (val Q) (val P).
Hypothesis hb : DPFusionSystem.arrow_compose b (linking_projection L f) =
  DPFusionSystem.arrow_identity F (val Q).

Lemma inverse_triangle :
    DPFusionSystem.arrow_compose b (linking_projection L f) =
    linking_projection L (linking_identity L Q).
Proof. by rewrite projection_identity hb. Qed.

Definition lifted_inverse : linking_hom L Q P := factorization inverse_triangle.

Lemma lifted_inverse_projection : linking_projection L lifted_inverse = b.
Proof. exact: factorization_projection. Qed.

Lemma lifted_inverse_hom : linking_compose L lifted_inverse f = linking_identity L Q.
Proof. exact: factorization_commutes. Qed.

Lemma lifted_hom_inverse : linking_compose L f lifted_inverse = linking_identity L P.
Proof.
apply: (@compose_right_injective S F L P P Q f).
by rewrite linking_assoc lifted_inverse_hom linking_id_right linking_id_left.
Qed.

Definition isomorphism_of_projection_retraction : @isomorphism (linking_category L) P Q :=
  @Build_isomorphism (linking_category L) P Q f lifted_inverse
    lifted_hom_inverse lifted_inverse_hom.

Lemma isomorphism_of_projection_retraction_hom :
    iso_hom isomorphism_of_projection_retraction = f.
Proof. reflexivity. Qed.
End ProjectedRetraction.

Section ProjectedIsomorphism.
Variables P Q : Obj.
Variable f : linking_hom L P Q.
Variable e : @isomorphism (centric_fusion_category F) P Q.
Hypothesis he : iso_hom e = linking_projection L f.

Lemma projected_inverse_triangle :
    DPFusionSystem.arrow_compose (iso_inv e) (linking_projection L f) =
    DPFusionSystem.arrow_identity F (val Q).
Proof. rewrite -he; exact (iso_inv_hom e). Qed.

Definition isomorphism_of_projection : @isomorphism (linking_category L) P Q :=
  isomorphism_of_projection_retraction projected_inverse_triangle.

Lemma isomorphism_of_projection_hom : iso_hom isomorphism_of_projection = f.
Proof. reflexivity. Qed.

Lemma isomorphism_of_projection_inv :
    linking_projection L (iso_inv isomorphism_of_projection) = iso_inv e.
Proof. exact: lifted_inverse_projection. Qed.
End ProjectedIsomorphism.

Section SurjectiveProjection.
Variables P Q : Obj.
Variable f : linking_hom L P Q.
Hypothesis hf : DPFusion.image (val (linking_projection L f)) = val Q.

Lemma projection_image_contains : val Q \subset DPFusion.image (val (linking_projection L f)).
Proof. by rewrite hf. Qed.

Definition projected_inverse_arrow : DPFusionSystem.arrow F (val Q) (val P) :=
  Sub (DPFusion.restrict (DPFusion.inverse (val (linking_projection L f))) projection_image_contains)
    (DPFusionSystem.restriction_allowed projection_image_contains
      (DPFusionSystem.inverse_closed (valP (linking_projection L f)))).

Lemma projected_inverse_arrow_triangle :
    DPFusionSystem.arrow_compose projected_inverse_arrow (linking_projection L f) =
    DPFusionSystem.arrow_identity F (val Q).
Proof.
apply DPFusionSystem.arrow_ext => x Qx.
rewrite DPFusion.compose_in // DPFusion.restrict_in // DPFusion.identity_in //.
apply DPFusion.inverse_cancel_right; by rewrite hf.
Qed.

Definition isomorphism_of_image_eq : @isomorphism (linking_category L) P Q :=
  isomorphism_of_projection_retraction projected_inverse_arrow_triangle.

Lemma isomorphism_of_image_eq_hom : iso_hom isomorphism_of_image_eq = f.
Proof. reflexivity. Qed.
End SurjectiveProjection.

(** A prescribed raw categorical isomorphism has a linking isomorphism
    above it, with the literal forward and inverse projections. *)
Definition lift_isomorphism (P Q : Obj)
    (e : @isomorphism (centric_fusion_category F) P Q) :
    @isomorphism (linking_category L) P Q :=
  isomorphism_of_projection (esym (chosen_lift_projection L (iso_hom e))).

Lemma lift_isomorphism_hom (P Q : Obj)
    (e : @isomorphism (centric_fusion_category F) P Q) :
    linking_projection L (iso_hom (lift_isomorphism e)) = iso_hom e.
Proof. exact: chosen_lift_projection. Qed.

Lemma lift_isomorphism_inv (P Q : Obj)
    (e : @isomorphism (centric_fusion_category F) P Q) :
    linking_projection L (iso_inv (lift_isomorphism e)) = iso_inv e.
Proof. exact: isomorphism_of_projection_inv. Qed.
End Isomorphisms.
End DPLinkingIsomorphisms.

Check DPLinkingIsomorphisms.isomorphism_of_projection_retraction.
Check DPLinkingIsomorphisms.isomorphism_of_image_eq.
Check DPLinkingIsomorphisms.lift_isomorphism.
Print Assumptions DPLinkingIsomorphisms.isomorphism_of_projection_retraction.
Print Assumptions DPLinkingIsomorphisms.isomorphism_of_image_eq.
Print Assumptions DPLinkingIsomorphisms.lift_isomorphism_inv.
