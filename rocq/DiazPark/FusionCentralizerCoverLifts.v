From mathcomp Require Import all_ssreflect all_fingroup center abelian generic_quotient.
From DiazPark Require Import Category CategoryFibration FusionMaps FusionSystems FusionSaturation
  FusionSaturationImage FusionOrbit FusionConjugacy FusionCentricBasics
  FusionCentralizerCompression FusionAbelianCentralizerExtension
  FusionCentralizerCover FusionCentralizerCoverProjection FusionCentralizerCoverCartesian.
Import DPFusion DPFusionOrbit DPFusionCentralizerCover DPFusionCentralizerCoverProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverLifts.
Section Lifts.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable X : centralized_object F p.
Variable B : elementary_object F p.
Variable theta : DPFusionSystem.arrow F (val B) (elementary (val X)).
Local Notation A := (DPFusion.image (val theta)).

Lemma image_abelian : abelian A.
Proof.
have /and3P[_ hB _] := valP B.
exact: morphim_abelian (abelem_abelian hB).
Qed.

Lemma extension_exists : exists g : DPFusion.map 'C(A)%G 'C(val B)%G,
  DPFusionSystem.allowed F g && [forall x in A, g x == DPFusion.inverse (val theta) x].
Proof.
have /and3P[_ _ hB] := valP B.
have [g [hg he]] := DPFusionAbelianCentralizerExtension.centralizer_extension_exists
  sat (DPFusionSystem.inverse_closed (valP theta))
  (DPFusionCentralizerCompression.inverse_image (val theta)) image_abelian hB.
exists g; apply/andP; split=> //; apply/forall_inP=> x Ax; apply/eqP; exact: he Ax.
Qed.

Definition extension : DPFusion.map 'C(A)%G 'C(val B)%G := xchoose extension_exists.
Lemma extension_allowed : DPFusionSystem.allowed F extension.
Proof. exact: (andP (xchooseP extension_exists)).1. Qed.
Lemma extensionE : {in A, extension =1 DPFusion.inverse (val theta)}.
Proof. move=> x Ax; apply/eqP; exact: (forall_inP (andP (xchooseP extension_exists)).2) x Ax. Qed.

Lemma carrier_sub_centralizer : carrier (val X) \subset 'C(A).
Proof.
apply: subset_trans (centS (DPFusion.image_sub (val theta))).
rewrite centsC.
exact: subset_trans (elementary_center (val X)) (subsetIr _ _).
Qed.

Definition restricted_extension := DPFusion.restrict extension carrier_sub_centralizer.
Lemma restricted_allowed : DPFusionSystem.allowed F restricted_extension.
Proof. exact: DPFusionSystem.restriction_allowed extension_allowed. Qed.
Definition target_group := DPFusion.image restricted_extension.
Lemma target_centric : DPFusionSystem.centric F target_group.
Proof. exact: DPFusionCentricBasics.centric_image restricted_allowed (carrier_centric (val X)). Qed.

Lemma extension_theta z : z \in val B -> restricted_extension (val theta z) = z.
Proof.
move=> Bz.
have Ez := DPFusion.map_into (val theta) Bz.
have Pz := subsetP (elementary_sub (val X)) _ Ez.
rewrite /restricted_extension DPFusion.restrict_in // extensionE ?DPFusion.image_mem //.
exact: DPFusion.inverse_cancel Bz.
Qed.

Lemma target_contains : val B \subset target_group.
Proof.
apply/subsetP=> z Bz; apply/morphimP; exists (val theta z).
- exact (subsetP (elementary_sub (val X)) _ (DPFusion.map_into (val theta) Bz)).
- exact (subsetP (elementary_sub (val X)) _ (DPFusion.map_into (val theta) Bz)).
- exact (esym (extension_theta Bz)).
Qed.

Lemma target_central : val B \subset 'Z(target_group).
Proof.
apply/subsetIP; split; first exact: target_contains.
rewrite centsC; exact: DPFusion.image_sub restricted_extension.
Qed.

Definition target_object : cover_object F p.
Proof.
exists (Sub target_group target_centric, val B); apply/and3P; split.
- have /and3P[hB _ _] := valP B; exact hB.
- have /and3P[_ hB _] := valP B; exact hB.
- exact: target_central.
Defined.
Definition centralized_target : centralized_object F p.
Proof.
exists target_object; have /and3P[_ _ hB] := valP B; exact hB.
Defined.

Definition raw_lift : DPFusionSystem.arrow F (carrier (val X)) (carrier target_object) :=
  Sub (DPFusion.to_image restricted_extension) (DPFusionSystem.image_closed restricted_allowed).
Lemma raw_lift_onto : DPFusion.image (val raw_lift) = carrier target_object.
Proof. exact: DPFusionSaturationImage.image_to_image. Qed.
Lemma raw_lift_theta z : z \in val B -> val raw_lift (val theta z) = z.
Proof.
move=> Bz; rewrite DPFusion.to_image_in; first exact: extension_theta Bz.
exact (subsetP (elementary_sub (val X)) _ (DPFusion.map_into (val theta) Bz)).
Qed.
Lemma raw_lift_condition : raw_condition raw_lift.
Proof.
apply/subsetP=> z Bz; apply/morphimP; exists (val theta z).
- exact (subsetP (elementary_sub (val X)) _ (DPFusion.map_into (val theta) Bz)).
- exact (DPFusion.map_into (val theta) Bz).
- exact (esym (raw_lift_theta Bz)).
Qed.
Definition lift_arrow : cover_hom (val X) target_object := cover_class raw_lift_condition.
Lemma lift_delta : delta lift_arrow = val theta.
Proof.
rewrite /lift_arrow delta_class; apply/esym/raw_delta_unique.
exact: raw_lift_theta.
Qed.
Lemma lift_cocartesian :
  @cocartesian (centralized_category F p) (opposite (elementary_category F p))
    (projection F p) X centralized_target lift_arrow.
Proof. exact (@DPFusionCentralizerCoverCartesian.onto_cover_cocartesian S F p X centralized_target raw_lift raw_lift_onto raw_lift_condition). Qed.
End Lifts.
End DPFusionCentralizerCoverLifts.



