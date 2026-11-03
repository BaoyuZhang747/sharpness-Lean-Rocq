(** Literal subgroup images under genuine simultaneous extensions. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionCentricBasics FusionConjugacy.
From DiazParkV16b Require Import NormalizerPointedSubgroupExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPNormalizerSubgroupExtensions.
Local Open Scope group_scope.

Module DPNormalizerSubgroupImages.
Section Images.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q R T : {group S}.
Variable f : DPFusion.map P Q.
Variable a : extension F R T f.

Definition subgroup_image : {group S} := (map_morphism (extension_map a) @* R)%G.

Lemma subgroup_image_sub : subgroup_image \subset T.
Proof.
apply/subsetP=> y /morphimP[x hv hx ->].
rewrite map_morphismE; exact: maps_into hx.
Qed.

Lemma subgroup_image_mem x : x \in R -> extension_map a x \in subgroup_image.
Proof. move=> hx; exact: mem_morphim (subsetP (subgroup_sub a) _ hx) hx. Qed.

Lemma restricted_image : image (restrict (extension_map a) (subgroup_sub a)) = subgroup_image.
Proof.
apply val_inj; apply/setP=> y; apply/morphimP/morphimP.
- move=> [x hx _ ->]; exists x; first exact: subsetP (subgroup_sub a) _ hx.
  + exact hx.
  + by rewrite !map_morphismE restrict_in.
- move=> [x hv hx ->]; exists x=> //.
  by rewrite !map_morphismE restrict_in.
Qed.

Lemma subgroup_image_centric : DPFusionSystem.centric F R -> DPFusionSystem.centric F subgroup_image.
Proof.
move=> hR; rewrite -restricted_image.
exact (DPFusionCentricBasics.centric_image
  (DPFusionSystem.restriction_allowed (subgroup_sub a) (extension_allowed a)) hR).
Qed.

Lemma subgroup_image_card : #|subgroup_image| = #|R|.
Proof.
rewrite -restricted_image; exact: DPFusionConjugacy.map_image_card.
Qed.

Lemma acting_image : map_morphism (extension_map a) @* P = image f.
Proof.
apply/setP=> y; apply/morphimP/morphimP.
- move=> [x hv hx ->]; exists x=> //; by rewrite !map_morphismE on_acting.
- move=> [x hx _ ->]; exists x; first exact: subsetP (acting_sub a) _ hx.
  + exact hx.
  + by rewrite !map_morphismE on_acting.
Qed.

Lemma subgroup_image_normalized (hP : P \subset 'N(R)) (hf : image f = Q) :
  Q \subset 'N(subgroup_image).
Proof.
have h := morphim_norms (map_morphism (extension_map a)) hP.
by rewrite acting_image hf in h.
Qed.

Definition image_extension : extension F R subgroup_image f :=
  @Build_extension S F R subgroup_image P Q f (carrier a) (acting_sub a)
    (subgroup_sub a) (extension_map a) (extension_allowed a) (on_acting a) subgroup_image_mem.
End Images.
End DPNormalizerSubgroupImages.
