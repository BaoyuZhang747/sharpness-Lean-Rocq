From mathcomp Require Import all_ssreflect all_fingroup center abelian generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation FusionSaturationImage
  FusionOrbit FusionConjugacy FusionCentricBasics FusionAbelianCentralizerExtension
  FusionCentralizerCover FusionCentralizerCoverIsomorphism.
Import DPFusion DPFusionOrbit DPFusionCentralizerCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverNormalization.
Section Normalization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable X : cover_object F p.
Local Notation E := (elementary X).
Definition target_elementary := DPFusionConjugacy.normalized_representative F E.
Lemma target_fully_centralized : DPFusionSystem.fully_centralized F target_elementary.
Proof.
exact: (DPFusionSaturation.saturation_fully_normalized sat
  (DPFusionConjugacy.normalized_representative_fully_normalized F E)).1.
Qed.
Lemma elementary_iso_exists : exists f : DPFusion.map E target_elementary,
  DPFusionSystem.allowed F f && (DPFusion.image f == target_elementary).
Proof.
apply/existsP; exact: (DPFusionConjugacy.normalized_representative_spec F E).1.
Qed.
Definition elementary_iso : DPFusion.map E target_elementary := xchoose elementary_iso_exists.
Lemma elementary_iso_allowed : DPFusionSystem.allowed F elementary_iso.
Proof. exact: (andP (xchooseP elementary_iso_exists)).1. Qed.
Lemma elementary_iso_onto : DPFusion.image elementary_iso = target_elementary.
Proof. apply/eqP; exact: (andP (xchooseP elementary_iso_exists)).2. Qed.
Lemma target_abelem : p.-abelem target_elementary.
Proof. rewrite -elementary_iso_onto; exact: morphim_abelem (elementary_abelem X). Qed.
Lemma target_nontrivial : target_elementary :!=: 1.
Proof.
rewrite -elementary_iso_onto.
change (~~ (DPFusion.map_morphism elementary_iso @* E == 1)).
rewrite (morphim_injm_eq1 (DPFusion.map_injm elementary_iso) (subxx E)).
exact: elementary_nontrivial.
Qed.
Lemma extension_exists : exists g : DPFusion.map 'C(E)%G 'C(target_elementary)%G,
  DPFusionSystem.allowed F g && [forall x in E, g x == elementary_iso x].
Proof.
have [g [hg he]] := DPFusionAbelianCentralizerExtension.centralizer_extension_exists
  sat elementary_iso_allowed elementary_iso_onto (abelem_abelian (elementary_abelem X))
  target_fully_centralized.
exists g; apply/andP; split=> //; apply/forall_inP=> x Ex; apply/eqP; exact: he Ex.
Qed.
Definition extension : DPFusion.map 'C(E)%G 'C(target_elementary)%G := xchoose extension_exists.
Lemma extension_allowed : DPFusionSystem.allowed F extension.
Proof. exact: (andP (xchooseP extension_exists)).1. Qed.
Lemma extensionE : {in E, extension =1 elementary_iso}.
Proof. move=> x Ex; apply/eqP; exact: (forall_inP (andP (xchooseP extension_exists)).2) x Ex. Qed.
Lemma carrier_sub_centralizer : carrier X \subset 'C(E).
Proof. rewrite centsC; exact: subset_trans (elementary_center X) (subsetIr _ _). Qed.
Definition restricted := DPFusion.restrict extension carrier_sub_centralizer.
Lemma restricted_allowed : DPFusionSystem.allowed F restricted.
Proof. exact: DPFusionSystem.restriction_allowed extension_allowed. Qed.
Definition target_group := DPFusion.image restricted.
Lemma target_centric : DPFusionSystem.centric F target_group.
Proof. exact: DPFusionCentricBasics.centric_image restricted_allowed (carrier_centric X). Qed.
Lemma elementary_image : DPFusion.map_morphism restricted @* E = target_elementary.
Proof.
have he : DPFusion.map_morphism restricted @* E = DPFusion.map_morphism elementary_iso @* E.
  rewrite !morphimEsub ?elementary_sub //.
  apply: eq_in_imset=> x Ex.
  change (restricted x = elementary_iso x).
  rewrite /restricted DPFusion.restrict_in ?(subsetP (elementary_sub X) _ Ex) //.
  exact: extensionE Ex.
exact (eq_trans he (congr1 val elementary_iso_onto)).
Qed.
Lemma target_contains : target_elementary \subset target_group.
Proof. rewrite -elementary_image; exact: morphimS (elementary_sub X). Qed.
Lemma target_central : target_elementary \subset 'Z(target_group).
Proof.
apply/subsetIP; split; first exact: target_contains.
rewrite centsC; exact: DPFusion.image_sub restricted.
Qed.
Definition target_object : cover_object F p.
Proof.
exists (Sub target_group target_centric, target_elementary); apply/and3P; split.
- exact: target_nontrivial.
- exact: target_abelem.
- exact: target_central.
Defined.
Definition normalized_object : centralized_object F p := Sub target_object target_fully_centralized.
Definition normalized_raw : DPFusionSystem.arrow F (carrier X) (carrier target_object) :=
  Sub (DPFusion.to_image restricted) (DPFusionSystem.image_closed restricted_allowed).
Lemma normalized_onto : DPFusion.image (val normalized_raw) = carrier target_object.
Proof. exact: DPFusionSaturationImage.image_to_image. Qed.
Lemma normalized_elementary_image :
  DPFusion.map_morphism (val normalized_raw) @* E = elementary target_object.
Proof.
rewrite -elementary_image !morphimEsub ?elementary_sub //.
apply: eq_in_imset=> x Ex; exact: DPFusion.to_image_in (subsetP (elementary_sub X) _ Ex).
Qed.
Definition normalization_iso : @isomorphism (cover_category F p) X (val normalized_object) :=
  DPFusionCentralizerCoverIsomorphism.raw_cover_iso normalized_onto normalized_elementary_image.
End Normalization.
End DPFusionCentralizerCoverNormalization.


