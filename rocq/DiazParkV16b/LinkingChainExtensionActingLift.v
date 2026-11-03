(** Compatible linking lifts chosen on the whole carrier of an actual pair
    extension, retaining its values on the acting subgroup. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionCentricBasics FusionSaturationImage.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFinite LinkingSystemRestrictions
  LinkingSystemCancellation LinkingSystemIsomorphisms LinkingChainObjects
  LinkingChainAutomorphisms NormalizerChainIndices NormalizerChainExtensions
  LinkingChainRestrictionMaps.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPCentricLinking DPLinkingFinite DPLinkingRestrictions
  DPLinkingCancellation DPLinkingIsomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPNormalizerChainExtensions DPLinkingChainRestrictionMaps.
Local Open Scope group_scope.

Module DPLinkingChainExtensionActingLift.
Section Lift.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable a : extension c d f.
Hypothesis cP : DPFusionSystem.centric F P.
Local Notation e := (indices a).

Definition carrier_object : DPFusionOrbit.centric_object F :=
  Sub (carrier a) (DPFusionCentricBasics.centric_overgroup (acting_sub a) cP).

Definition ambient_object : DPFusionOrbit.centric_object F :=
  Sub [set: S]%G (DPFusionCentricBasics.centric_overgroup (subsetT P) cP).

Definition carrier_arrow : DPFusionSystem.arrow F (val carrier_object) (val ambient_object) :=
  Sub (extension_map a) (extension_allowed a).

Definition carrier_lift : linking_hom L carrier_object ambient_object := chosen_lift L carrier_arrow.

Lemma carrier_lift_projection : val (linking_projection L carrier_lift) = extension_map a.
Proof. by rewrite /carrier_lift chosen_lift_projection. Qed.

Lemma entry_restriction_image (i : 'I_(length d).+1) :
  image (DPFusion.restrict (val (linking_projection L carrier_lift)) (entry_sub_carrier a i)) =
  subgroup d i.
Proof.
apply val_inj.
change (map_morphism (DPFusion.restrict (val (linking_projection L carrier_lift))
  (entry_sub_carrier a i)) @* subgroup c (index e i) = subgroup d i).
rewrite /DPFusion.restrict of_morphism_image im_restrm carrier_lift_projection.
exact: entry_images.
Qed.

Lemma entry_restriction_image_sub (i : 'I_(length d).+1) :
  image (DPFusion.restrict (val (linking_projection L carrier_lift)) (entry_sub_carrier a i))
    \subset subgroup d i.
Proof. by rewrite entry_restriction_image. Qed.

Definition entry_lift (i : 'I_(length d).+1) : linking_hom L (entry c (index e i)) (entry d i) :=
  @DPLinkingRestrictions.restriction S F L carrier_object ambient_object
    (entry c (index e i)) (entry d i) carrier_lift (entry_sub_carrier a i)
    (subsetT (subgroup d i)) (entry_restriction_image_sub i).

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
by rewrite corestrict_in // restrict_in // carrier_lift_projection.
Qed.

Definition entry_lift_iso (i : 'I_(length d).+1) :
  @isomorphism (linking_category L) (entry c (index e i)) (entry d i) :=
  isomorphism_of_image_eq (entry_lift_image i).

Lemma source_inclusion_compose (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij))
    (@DPCentricLinking.inclusion S F L (entry c (index e j)) carrier_object (entry_sub_carrier a j)) =
  @DPCentricLinking.inclusion S F L (entry c (index e i)) carrier_object (entry_sub_carrier a i).
Proof.
change (linking_compose L (DPCentricLinking.inclusion L (entry_mono (index_mono e hij)))
  (@DPCentricLinking.inclusion S F L (entry c (index e j)) carrier_object (entry_sub_carrier a j)) =
  @DPCentricLinking.inclusion S F L (entry c (index e i)) carrier_object (entry_sub_carrier a i)).
transitivity (@DPCentricLinking.inclusion S F L (entry c (index e i)) carrier_object
  (subset_trans (entry_mono (index_mono e hij)) (entry_sub_carrier a j))).
- exact: inclusion_compose.
- f_equal; exact: Prop_irrelevance.
Qed.

Lemma target_inclusion_compose (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L d i j hij)
    (@DPCentricLinking.inclusion S F L (entry d j) ambient_object (subsetT (subgroup d j))) =
  @DPCentricLinking.inclusion S F L (entry d i) ambient_object (subsetT (subgroup d i)).
Proof.
change (linking_compose L (DPCentricLinking.inclusion L (entry_mono hij))
  (@DPCentricLinking.inclusion S F L (entry d j) ambient_object (subsetT (subgroup d j))) =
  @DPCentricLinking.inclusion S F L (entry d i) ambient_object (subsetT (subgroup d i))).
transitivity (@DPCentricLinking.inclusion S F L (entry d i) ambient_object
  (subset_trans (entry_mono hij) (subsetT (subgroup d j)))).
- exact: inclusion_compose.
- f_equal; exact: Prop_irrelevance.
Qed.

Lemma entry_lift_square (i : 'I_(length d).+1) :
  linking_compose L (entry_lift i) (@DPCentricLinking.inclusion S F L (entry d i) ambient_object (subsetT (subgroup d i))) =
  linking_compose L (@DPCentricLinking.inclusion S F L (entry c (index e i)) carrier_object (entry_sub_carrier a i)) carrier_lift.
Proof. exact: restriction_square. Qed.

Lemma entry_lift_compatible (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij)) (iso_hom (entry_lift_iso j)) =
  linking_compose L (iso_hom (entry_lift_iso i)) (@chain_inclusion S F L d i j hij).
Proof.
apply (@compose_right_injective S F L (entry c (index e i)) (entry d j) ambient_object
  (@DPCentricLinking.inclusion S F L (entry d j) ambient_object (subsetT (subgroup d j)))).
change (linking_compose L
  (linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij)) (entry_lift j))
  (@DPCentricLinking.inclusion S F L (entry d j) ambient_object (subsetT (subgroup d j))) =
  linking_compose L (linking_compose L (entry_lift i) (@chain_inclusion S F L d i j hij))
  (@DPCentricLinking.inclusion S F L (entry d j) ambient_object (subsetT (subgroup d j)))).
rewrite !linking_assoc target_inclusion_compose !entry_lift_square
  -linking_assoc source_inclusion_compose; reflexivity.
Qed.

Definition extension_chain_map : chain_map L c d :=
  @Build_chain_map S F L c d e entry_lift_iso entry_lift_compatible.

Lemma extension_chain_map_indices : selected_indices extension_chain_map = indices a.
Proof. reflexivity. Qed.

Theorem extension_chain_map_projection i x (hx : x \in subgroup c (index e i)) :
  val (linking_projection L (iso_hom (entry_isomorphism extension_chain_map i))) x =
    extension_map a x.
Proof. exact: entry_lift_projectionE hx. Qed.
End Lift.
End DPLinkingChainExtensionActingLift.
