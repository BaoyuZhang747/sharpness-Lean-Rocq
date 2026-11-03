(** A chain-preserving actual fusion extension induces an actual compatible
    linking-chain automorphism by restricting one exact linking lift. *)
From mathcomp Require Import all_boot all_fingroup boolp action.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionAutomorphisms.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFinite LinkingSystemRestrictions
  LinkingSystemAutomorphisms LinkingSystemAutomorphismProjection LinkingChainObjects
  LinkingChainAutomorphisms NormalizerChainStabilizer
  LinkingChainAutomorphismStabilizerRestrictions ChainNormalizerFusionExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPCentricLinking DPLinkingFinite DPLinkingRestrictions
  DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainStabilizer DPLinkingChainStabilizerRestrictions DPChainNormalizerFusion.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module DPChainNormalizerFusionLift.
Section Lift.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variables P Q : {group S}.
Variable b : DPFusion.map (join_subgroup c P) (join_subgroup c Q).
Hypothesis hb : DPFusionSystem.allowed F b.
Hypothesis hc : @preserves_chain S F c P Q b.

Definition extension_arrow : DPFusionSystem.arrow F (join_subgroup c P) (join_subgroup c Q) := Sub b hb.
Definition extension_lift : linking_hom L (join_object c P) (join_object c Q) :=
  @chosen_lift S F L (join_object c P) (join_object c Q) extension_arrow.

Lemma extension_lift_projection : val (linking_projection L extension_lift) = b.
Proof. by rewrite /extension_lift chosen_lift_projection. Qed.

Lemma top_restriction_image :
  DPFusion.image (DPFusion.restrict (val (linking_projection L extension_lift)) (top_sub_join c P))
    \subset val (top c).
Proof.
apply/subsetP=> y /morphimP[x _ hx ->].
rewrite DPFusion.map_morphismE DPFusion.restrict_in // extension_lift_projection.
exact (@extension_value_in_entry S F c P Q b hc ord_max x hx).
Qed.

Definition top_action : automorphism_group L (top c) :=
  @restriction S F L (join_object c P) (join_object c Q) (top c) (top c)
    extension_lift (top_sub_join c P) (top_sub_join c Q) top_restriction_image.

Lemma top_action_value x (hx : x \in val (top c)) :
  DPFusion.map_fun (val (linking_projection L top_action)) x = b x.
Proof.
rewrite /top_action restriction_projection /raw_restriction /=.
rewrite DPFusion.corestrict_in // DPFusion.restrict_in //.
exact (congr1 (fun g => DPFusion.map_fun g x) extension_lift_projection).
Qed.

Lemma top_action_square :
  linking_compose L top_action (@inclusion S F L (top c) (join_object c Q) (top_sub_join c Q)) =
    linking_compose L (@inclusion S F L (top c) (join_object c P) (top_sub_join c P)) extension_lift.
Proof. exact: restriction_square. Qed.

Lemma top_action_stabilizes :
  val (DPLinkingAutomorphismProjection.projection L (top c) top_action) \in fusion_stabilizer c.
Proof.
apply/setIP; split; first exact: valP.
apply/bigcapP=> i _; rewrite !inE; apply/subsetP=> x hx; rewrite inE /=.
change (is_true (val (DPLinkingAutomorphismProjection.projection L (top c) top_action) x
  \in subgroup c i)).
rewrite (DPLinkingAutomorphismProjection.projection_apply _
  (subsetP (@entry_sub_top S F c i) _ hx)) top_action_value.
- exact (@extension_value_in_entry S F c P Q b hc i x hx).
- exact: subsetP (@entry_sub_top S F c i) _ hx.
Qed.

Definition chain_action : chain_automorphism_group L c :=
  @compatible_lift S F L c top_action top_action_stabilizes.

Lemma chain_action_top : projection ord_max chain_action = top_action.
Proof. exact: compatible_lift_top. Qed.

End Lift.
End DPChainNormalizerFusionLift.
