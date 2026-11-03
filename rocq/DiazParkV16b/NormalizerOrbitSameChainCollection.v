(** The actual ambient-centric collection maps fully faithfully onto the
    same-chain pair category.  All raw maps are the literal subgroup charts. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionSaturation FusionCentralizerMaps FusionSubsystemOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainNormalizer
  ChainNormalizerFusionExtension ChainNormalizerFusionModel ChainNormalizerFusionOrbit
  NormalizerChainSameExtension NormalizerOrbitPairCategory NormalizerOrbitSameChainCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPFusionSubgroup DPLinkingChains DPNormalizerChain
  DPChainNormalizerFusionModel DPChainNormalizerFusionOrbit.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerOrbitSameChainCollection.
Section Collection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation N := [the finGroupType of [subg (normalizer c)]%type].
Local Notation H := (local_system L c).
Local Notation X := (collection_category L c).
Local Notation Y := (DPNormalizerOrbitSameChain.category c).

Definition to_same_object (P : X) : Y :=
  Sub (@collection_ambient_object S F c P) (ambient_sub (val P)).

Definition from_same_subgroup (P : Y) : {group N} :=
  ((@sgval _ (normalizer c)) @*^-1 val (DPNormalizerOrbitSameChain.acting P))%G.

Lemma from_same_ambient (P : Y) : ambient (from_same_subgroup P) =
    val (DPNormalizerOrbitSameChain.acting P).
Proof.
apply val_inj; apply: morphpreK.
rewrite im_sgval; exact: DPNormalizerOrbitSameChain.acting_normalizes.
Qed.

Definition from_same_object (P : Y) : X.
Proof.
apply: (Sub (from_same_subgroup P)).
rewrite /ambient_centric from_same_ambient; exact: valP (DPNormalizerOrbitSameChain.acting P).
Defined.

Lemma same_object_roundtrip (P : Y) : to_same_object (from_same_object P) = P.
Proof. apply val_inj; apply val_inj; exact: from_same_ambient. Qed.

Lemma collection_object_roundtrip (P : X) : from_same_object (to_same_object P) = P.
Proof. apply val_inj; apply: ambient_injective; exact: from_same_ambient. Qed.

Lemma raw_lift_compatible (P Q : X) (f : DPFusionSystem.arrow H (val P) (val Q)) :
  DPNormalizerOrbitPair.compatible
    (A := DPNormalizerOrbitSameChain.point (to_same_object P))
    (B := DPNormalizerOrbitSameChain.point (to_same_object Q))
    (orbit_class (DPFusionSubsystem.ambient_arrow (@local_ambient_allowed S F L c p sat) f)).
Proof.
apply (proj2 (@DPNormalizerOrbitSameChain.hom_extension_iff S F c
  (to_same_object P) (to_same_object Q) _)).
exists (DPFusionSubsystem.ambient_arrow (@local_ambient_allowed S F L c p sat) f).
split; first reflexivity.
rewrite -(@local_allowed_extension S F L c p sat); exact: valP f.
Qed.

Definition to_same_map (P Q : X) (f : hom X P Q) : hom Y (to_same_object P) (to_same_object Q).
Proof.
apply: (Sub (fmap (@collection_ambient_functor S F L c p sat) f)).
apply/asboolP.
change (DPNormalizerOrbitPair.compatible
  (A := DPNormalizerOrbitSameChain.point (to_same_object P))
  (B := DPNormalizerOrbitSameChain.point (to_same_object Q))
  (orbit_class (DPFusionSubsystem.ambient_arrow (@local_ambient_allowed S F L c p sat) (repr f)))).
exact: raw_lift_compatible.
Defined.

Definition to_same : functor X Y.
Proof.
refine (@Build_functor X Y to_same_object to_same_map _ _).
- move=> P; apply val_inj; exact (fmap_id (@collection_ambient_functor S F L c p sat) P).
- move=> P Q U f g; apply val_inj;
  exact (fmap_compose (@collection_ambient_functor S F L c p sat) f g).
Defined.

Lemma to_same_ambient (P Q : X) (f : hom X P Q) :
  val (fmap to_same f) = fmap (@collection_ambient_functor S F L c p sat) f.
Proof. reflexivity. Qed.

Lemma to_same_class (P Q : X) (f : DPFusionSystem.arrow H (val P) (val Q)) :
  val (fmap to_same (orbit_class f)) =
  orbit_class (DPFusionSubsystem.ambient_arrow (@local_ambient_allowed S F L c p sat) f).
Proof. exact: collection_ambient_class. Qed.

Lemma to_same_faithful (P Q : X) : injective (@fmap _ _ to_same P Q).
Proof.
move=> f g h; apply (@collection_ambient_faithful S F L c p sat P Q).
exact (congr1 (fun a : hom Y (to_same_object P) (to_same_object Q) => val a) h).
Qed.

Lemma lift_lower (P Q : {group N}) (f : DPFusion.map (ambient P) (ambient Q)) :
  lift (lower f) = f.
Proof.
apply: map_ext=> x hx.
have hv := ambient_subgK hx; rewrite -{1}hv liftE ?ambient_repr // lowerE ?ambient_repr // hv.
reflexivity.
Qed.

Lemma to_same_full (P Q : X) (f : hom Y (to_same_object P) (to_same_object Q)) :
  exists g : hom X P Q, fmap to_same g = f.
Proof.
have [g [hg hExt]] := proj1 (@DPNormalizerOrbitSameChain.hom_extension_iff S F c
  (to_same_object P) (to_same_object Q) (val f)) (DPNormalizerOrbitPair.hom_compatible f).
have hlow : DPFusionSystem.allowed H (lower (val g)).
  rewrite (@local_allowed_extension S F L c p sat) lift_lower; exact hExt.
pose b : DPFusionSystem.arrow H (val P) (val Q) := Sub (lower (val g)) hlow.
exists (orbit_class b); apply val_inj; rewrite to_same_class -hg; congr (orbit_class _).
apply val_inj; exact: lift_lower.
Qed.

End Collection.
End DPNormalizerOrbitSameChainCollection.
