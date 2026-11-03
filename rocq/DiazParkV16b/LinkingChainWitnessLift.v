(** Every genuine selected-chain fusion extension lifts to compatible
    linking isomorphisms, hence to the actual chain-automorphism restriction. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturationImage.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFinite LinkingSystemRestrictions
  LinkingSystemCancellation LinkingSystemIsomorphisms LinkingChainObjects
  LinkingChainAutomorphisms NormalizerChainIndices NormalizerChainExtensions
  NormalizerChainRelations LinkingChainRestrictionMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPCentricLinking DPLinkingFinite DPLinkingRestrictions
  DPLinkingCancellation DPLinkingIsomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPNormalizerChainExtensions DPNormalizerChainRelations
  DPLinkingChainRestrictionMaps.
Local Open Scope group_scope.

Module DPLinkingChainWitnessLift.
Section Lift.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable a : chain_witness c d.
Local Notation e := (indices a).
Local Notation P := (entry c (index e ord_max)).
Local Notation Q := (top d).

Definition selected_top_restriction := DPFusion.restrict (extension_map a) (chain_sub a).

Lemma selected_top_image : image selected_top_restriction = val Q.
Proof.
apply val_inj.
change (map_morphism (DPFusion.restrict (extension_map a) (chain_sub a)) @* val P = val Q).
rewrite /DPFusion.restrict of_morphism_image im_restrm.
exact (entry_images a ord_max).
Qed.

Lemma selected_top_image_sub : image selected_top_restriction \subset val Q.
Proof. by rewrite selected_top_image. Qed.

Definition selected_top_map : DPFusion.map (val P) (val Q) :=
  corestrict selected_top_image_sub.

Lemma selected_top_map_allowed : DPFusionSystem.allowed F selected_top_map.
Proof.
apply DPFusionSystem.corestriction_allowed.
exact: DPFusionSystem.restriction_allowed (extension_allowed a).
Qed.

Lemma selected_top_mapE x : x \in val P -> selected_top_map x = extension_map a x.
Proof. move=> hx; by rewrite /selected_top_map corestrict_in // /selected_top_restriction restrict_in. Qed.

Definition selected_top_arrow : DPFusionSystem.arrow F (val P) (val Q) :=
  Sub selected_top_map selected_top_map_allowed.

Definition selected_top_lift : linking_hom L P Q := chosen_lift L selected_top_arrow.

Lemma selected_top_lift_projection : val (linking_projection L selected_top_lift) = selected_top_map.
Proof. by rewrite /selected_top_lift chosen_lift_projection. Qed.

Definition source_sub_top (i : 'I_(length d).+1) :
  subgroup c (index e i) \subset val P :=
  @entry_mono S F c (index e i) (index e ord_max)
    (@index_mono S F c d e i ord_max (leq_ord i)).

Lemma entry_restriction_image (i : 'I_(length d).+1) :
  image (DPFusion.restrict (val (linking_projection L selected_top_lift)) (source_sub_top i)) = subgroup d i.
Proof.
apply val_inj.
change (map_morphism (DPFusion.restrict (val (linking_projection L selected_top_lift))
  (source_sub_top i)) @* subgroup c (index e i) = subgroup d i).
rewrite /DPFusion.restrict of_morphism_image im_restrm selected_top_lift_projection.
rewrite -(entry_images a i); apply: eq_in_morphim.
- rewrite (setIidPr (source_sub_top i)) (setIidPr (entry_sub_carrier a i)); reflexivity.
- move=> x hx; exact: selected_top_mapE (subsetP (source_sub_top i) _ hx).
Qed.

Lemma entry_restriction_image_sub (i : 'I_(length d).+1) :
  image (DPFusion.restrict (val (linking_projection L selected_top_lift)) (source_sub_top i))
    \subset subgroup d i.
Proof. by rewrite entry_restriction_image. Qed.

Definition entry_lift (i : 'I_(length d).+1) : linking_hom L (entry c (index e i)) (entry d i) :=
  @DPLinkingRestrictions.restriction S F L P Q (entry c (index e i)) (entry d i)
    selected_top_lift (source_sub_top i) (@entry_sub_top S F d i) (entry_restriction_image_sub i).

Lemma entry_lift_image (i : 'I_(length d).+1) :
  image (val (linking_projection L (entry_lift i))) = subgroup d i.
Proof.
rewrite /entry_lift restriction_projection.
change (image (DPFusion.corestrict (entry_restriction_image_sub i)) = subgroup d i).
rewrite DPFusionSaturationImage.image_corestrict; exact: entry_restriction_image.
Qed.

Lemma entry_lift_projectionE (i : 'I_(length d).+1) x
  (hx : x \in subgroup c (index e i)) :
  val (linking_projection L (entry_lift i)) x = extension_map a x.
Proof.
rewrite /entry_lift restriction_projection.
change (DPFusion.corestrict (entry_restriction_image_sub i) x = extension_map a x).
rewrite corestrict_in // restrict_in // selected_top_lift_projection.
exact: selected_top_mapE (subsetP (source_sub_top i) _ hx).
Qed.

Definition entry_lift_iso (i : 'I_(length d).+1) :
  @isomorphism (linking_category L) (entry c (index e i)) (entry d i) :=
  isomorphism_of_image_eq (entry_lift_image i).

Lemma source_inclusion_compose (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij))
    (DPCentricLinking.inclusion L (source_sub_top j)) =
  DPCentricLinking.inclusion L (source_sub_top i).
Proof.
change (linking_compose L (DPCentricLinking.inclusion L (entry_mono (index_mono e hij)))
  (DPCentricLinking.inclusion L (source_sub_top j)) = DPCentricLinking.inclusion L (source_sub_top i)).
transitivity (DPCentricLinking.inclusion L
  (subset_trans (entry_mono (index_mono e hij)) (source_sub_top j))).
- exact: inclusion_compose.
- congr (DPCentricLinking.inclusion L _); exact: Prop_irrelevance.
Qed.

Lemma target_inclusion_compose (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L d i j hij)
    (DPCentricLinking.inclusion L (@entry_sub_top S F d j)) =
  DPCentricLinking.inclusion L (@entry_sub_top S F d i).
Proof.
change (linking_compose L (DPCentricLinking.inclusion L (entry_mono hij))
  (DPCentricLinking.inclusion L (@entry_sub_top S F d j)) =
  DPCentricLinking.inclusion L (@entry_sub_top S F d i)).
transitivity (DPCentricLinking.inclusion L
  (subset_trans (entry_mono hij) (@entry_sub_top S F d j))).
- exact: inclusion_compose.
- congr (DPCentricLinking.inclusion L _); exact: Prop_irrelevance.
Qed.

Lemma entry_lift_square (i : 'I_(length d).+1) :
  linking_compose L (entry_lift i) (DPCentricLinking.inclusion L (@entry_sub_top S F d i)) =
  linking_compose L (DPCentricLinking.inclusion L (source_sub_top i)) selected_top_lift.
Proof. exact: restriction_square. Qed.

Lemma entry_lift_compatible (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij)) (iso_hom (entry_lift_iso j)) =
  linking_compose L (iso_hom (entry_lift_iso i)) (@chain_inclusion S F L d i j hij).
Proof.
apply (@compose_right_injective S F L (entry c (index e i)) (entry d j) Q
  (DPCentricLinking.inclusion L (@entry_sub_top S F d j))).
change (linking_compose L
  (linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij)) (entry_lift j))
  (DPCentricLinking.inclusion L (@entry_sub_top S F d j)) =
  linking_compose L (linking_compose L (entry_lift i) (@chain_inclusion S F L d i j hij))
  (DPCentricLinking.inclusion L (@entry_sub_top S F d j))).
rewrite !linking_assoc target_inclusion_compose !entry_lift_square
  -linking_assoc source_inclusion_compose; reflexivity.
Qed.

Definition witness_chain_map : chain_map L c d :=
  @Build_chain_map S F L c d e entry_lift_iso entry_lift_compatible.

Lemma witness_chain_map_indices : selected_indices witness_chain_map = indices a.
Proof. reflexivity. Qed.

Theorem witness_chain_map_projection i x (hx : x \in subgroup c (index e i)) :
  val (linking_projection L (iso_hom (entry_isomorphism witness_chain_map i))) x =
    extension_map a x.
Proof. exact: entry_lift_projectionE hx. Qed.

Definition witness_restriction_morphism :
  {morphism [set: chain_automorphism_group L c] >-> chain_automorphism_group L d} :=
  restriction_morphism witness_chain_map.
End Lift.
End DPLinkingChainWitnessLift.
