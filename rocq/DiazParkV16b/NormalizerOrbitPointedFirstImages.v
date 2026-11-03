(** Carrier-level first-image equality for actual arrows in the first-entry comma. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices NormalizerChainExtensions
  NormalizerOrbitPairCategory NormalizerOrbitCommaImageObjects NormalizerOrbitPointedFirst
  NormalizerPointedSubgroups NormalizerPointedSubgroupExtensions NormalizerPointedSubgroupImages
  NormalizerPointedSubgroupImageFactorization NormalizerPointedSubgroupImageComposition
  NormalizerPointedSubgroupImageLaws NormalizerOrbitPointedFirstComma.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPFusionOrbit DPNormalizerPointedSubgroupImageFactorization
  DPNormalizerOrbitPointedFirstComma.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerOrbitPointedFirstImages.
Section Carrier.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variables Q T : {group S}.
Variable g : DPFusion.map Q T.
Variable a : DPNormalizerChainExtensions.extension c d g.

Lemma first_sub_carrier : val (bottom c) \subset DPNormalizerChainExtensions.carrier a.
Proof.
apply: subset_trans (DPNormalizerChainExtensions.entry_sub_carrier a ord0).
exact (@entry_mono S F c ord0 _ (leq0n _)).
Qed.

Lemma first_maps_into x : x \in val (bottom c) ->
  DPNormalizerChainExtensions.extension_map a x \in val (bottom d).
Proof.
move=> hx; change (DPNormalizerChainExtensions.extension_map a x \in subgroup d ord0).
rewrite -(DPNormalizerChainExtensions.entry_images a ord0).
exact: mem_morphim (subsetP first_sub_carrier _ hx)
  (subsetP (@entry_mono S F c ord0 _ (leq0n _)) _ hx).
Qed.

Definition chain_first_extension :
  DPNormalizerSubgroupExtensions.extension F (val (bottom c)) (val (bottom d)) g :=
  @DPNormalizerSubgroupExtensions.Build_extension S F (val (bottom c)) (val (bottom d))
    Q T g (DPNormalizerChainExtensions.carrier a) (DPNormalizerChainExtensions.acting_sub a)
    first_sub_carrier (DPNormalizerChainExtensions.extension_map a)
    (DPNormalizerChainExtensions.extension_allowed a)
    (DPNormalizerChainExtensions.on_acting a) first_maps_into.

Lemma chain_first_extension_map :
  DPNormalizerSubgroupExtensions.extension_map chain_first_extension =
    DPNormalizerChainExtensions.extension_map a.
Proof. reflexivity. Qed.
End Carrier.

Section FirstImages.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable P : centric_object F.
Local Notation CP := (DPNormalizerOrbitCommaImage.pointed_category P).
Local Notation SP := (DPNormalizerPointedSubgroups.pointed_category P).
Local Notation OC := (centric_orbit_category F).
Variable B : SP.
Variable Y : first_points B.
Variable X : first_under B.
Variable f : hom (first_under B) (point_under Y) X.
Let CY := DPNormalizerOrbitCommaImage.pointed_pair (point_chain Y).
Let CX := DPNormalizerOrbitCommaImage.pointed_pair (costructured_source X).
Variable g : DPFusionSystem.arrow F (val (DPNormalizerOrbitPair.acting CY))
  (val (DPNormalizerOrbitPair.acting CX)).
Hypothesis hg : orbit_class g = val (costructured_map (costructured_map f)).
Variable a : DPNormalizerChainExtensions.extension (DPNormalizerOrbitPair.chain_of CY)
  (DPNormalizerOrbitPair.chain_of CX) (val g).

Theorem first_carrier_image :
  map_morphism (DPNormalizerChainExtensions.extension_map a) @*
      val (bottom (DPNormalizerOrbitPair.chain_of CY)) = arrow_image (costructured_arrow X).
Proof.
pose b := data_extension (chosen_data (iso_hom (point_iso Y))).
pose c := chain_first_extension a.
have hb : DPNormalizerSubgroupImages.subgroup_image b =
    DPNormalizerPointedSubgroups.subgroup
      (fobj (DPNormalizerOrbitPointedFirst.first_functor P) (point_chain Y)) :=
  arrow_image_eq_target (iso_hom (point_iso Y)) (iso_inv (point_iso Y)).
pose raw := DPFusionSystem.arrow_compose (data_raw (chosen_data (iso_hom (point_iso Y)))) g.
have hraw : @Category.compose OC P (DPNormalizerPointedSubgroups.acting B)
    (DPNormalizerOrbitPair.acting CX) (iso_hom (DPNormalizerPointedSubgroups.point B))
    (orbit_class raw) = iso_hom (DPNormalizerOrbitCommaImage.pointed_iso (costructured_source X)).
  rewrite /raw -orbit_compose_class -Category.compose_assoc data_point hg.
  exact (costructured_commutes (costructured_map f)).
have he := DPNormalizerPointedSubgroupImageLaws.arrow_image_eq_extension pS sat
  (costructured_arrow X) hraw (DPNormalizerSubgroupExtensions.compose_extension b c).
rewrite he DPNormalizerSubgroupImageComposition.image_of_composition hb.
rewrite /c chain_first_extension_map.
reflexivity.
Qed.
End FirstImages.
End DPNormalizerOrbitPointedFirstImages.
