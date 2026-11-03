(** A top linking automorphism preserving a centric chain has its actual,
    uniquely compatible restrictions to all entries. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionSaturation FusionAutomorphisms.
From DiazParkV16b Require Import LinkingSystem LinkingSystemRestrictions
  LinkingSystemCancellation LinkingSystemAutomorphisms
  LinkingSystemAutomorphismProjection LinkingChainObjects
  LinkingChainAutomorphisms NormalizerChainStabilizer.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingRestrictions DPLinkingCancellation
  DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainStabilizer.
Local Open Scope group_scope.

Module DPLinkingChainStabilizerRestrictions.
Section Restrictions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation I := 'I_(length c).+1.
Local Notation G := (automorphism_group L (top c)).
Local Notation pr := (DPLinkingAutomorphismProjection.projection L (top c)).

Lemma inclusion_to_top_compose (i j : I) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L c i j hij) (inclusion L (@entry_sub_top S F c j)) =
    inclusion L (@entry_sub_top S F c i).
Proof.
change (linking_compose L (inclusion L (entry_mono hij))
  (inclusion L (@entry_sub_top S F c j)) = inclusion L (@entry_sub_top S F c i)).
transitivity (inclusion L (subset_trans (entry_mono hij) (@entry_sub_top S F c j))).
- exact: inclusion_compose.
- congr (inclusion L _); exact: Prop_irrelevance.
Qed.

Lemma inclusion_top_identity : inclusion L (@entry_sub_top S F c ord_max) = linking_identity L (top c).
Proof.
have hp : @entry_sub_top S F c ord_max = subxx (val (top c)) := Prop_irrelevance _ _.
rewrite hp; exact: inclusion_identity.
Qed.

Variable a : G.
Hypothesis ha : val (pr a) \in fusion_stabilizer c.

Lemma restriction_image (i : I) :
  DPFusion.image (DPFusion.restrict (val (linking_projection L a)) (@entry_sub_top S F c i))
    \subset subgroup c i.
Proof.
have /fusion_stabilizerP [_ hfix] := ha.
apply/subsetP=> y /morphimP [x _ hx ->].
rewrite DPFusion.map_morphismE DPFusion.restrict_in //.
have hxT : x \in val (top c) := subsetP (@entry_sub_top S F c i) _ hx.
rewrite -(DPLinkingAutomorphismProjection.projection_apply a hxT).
by rewrite hfix.
Qed.

Definition entry_restriction (i : I) : automorphism_group L (entry c i) :=
  @restriction S F L (top c) (top c) (entry c i) (entry c i)
    a (@entry_sub_top S F c i) (@entry_sub_top S F c i) (restriction_image i).

Lemma entry_restriction_square (i : I) :
  linking_compose L (entry_restriction i) (inclusion L (@entry_sub_top S F c i)) =
    linking_compose L (inclusion L (@entry_sub_top S F c i)) a.
Proof. exact: restriction_square. Qed.

Lemma entry_restriction_compatible (i j : I) (hij : i <= j) :
  linking_compose L (entry_restriction i) (@chain_inclusion S F L c i j hij) =
    linking_compose L (@chain_inclusion S F L c i j hij) (entry_restriction j).
Proof.
apply (@compose_right_injective S F L (entry c i) (entry c j) (top c)
  (inclusion L (@entry_sub_top S F c j))).
rewrite !linking_assoc inclusion_to_top_compose !entry_restriction_square.
by rewrite -linking_assoc inclusion_to_top_compose.
Qed.

Lemma entry_restriction_top : entry_restriction ord_max = a.
Proof.
have hs := entry_restriction_square ord_max.
by rewrite inclusion_top_identity linking_id_left linking_id_right in hs.
Qed.

Definition restriction_tuple : tuple_group L c := [ffun i => entry_restriction i].

Lemma restriction_tuple_compatible : compatible restriction_tuple.
Proof.
apply/compatibleP=> i j hij; rewrite /restriction_tuple !ffunE.
exact: entry_restriction_compatible.
Qed.

Definition compatible_lift : chain_automorphism_group L c.
Proof.
apply: (Sub restriction_tuple); rewrite inE; exact: restriction_tuple_compatible.
Defined.

Lemma compatible_lift_projection (i : I) :
  DPLinkingChainAutomorphisms.projection i compatible_lift = entry_restriction i.
Proof. rewrite /DPLinkingChainAutomorphisms.projection /compatible_lift /= /restriction_tuple ffunE; reflexivity. Qed.

Theorem compatible_lift_top : DPLinkingChainAutomorphisms.projection ord_max compatible_lift = a.
Proof. rewrite compatible_lift_projection; exact: entry_restriction_top. Qed.
End Restrictions.
End DPLinkingChainStabilizerRestrictions.

Check DPLinkingChainStabilizerRestrictions.compatible_lift.
Print Assumptions DPLinkingChainStabilizerRestrictions.compatible_lift_top.
