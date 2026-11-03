(** The literal full same-chain part of the normalizer pair category. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryFinite FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer
  NormalizerOrbitPairCategory NormalizerChainSameExtension ChainNormalizerFusionExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPLinkingChains DPNormalizerChain.
Local Open Scope group_scope.

Module DPNormalizerOrbitSameChain.
Section Same.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.

Definition object : finType := [the finType of
  {P : centric_object F | val P \subset normalizer c}].
Definition acting (P : object) : centric_object F := val P.
Lemma acting_normalizes (P : object) : val (acting P) \subset normalizer c.
Proof. exact: valP P. Qed.

Definition point (P : object) : DPNormalizerOrbitPair.object F :=
  Sub (acting P, c) (acting_normalizes P).

Lemma point_acting P : DPNormalizerOrbitPair.acting (point P) = acting P.
Proof. reflexivity. Qed.
Lemma point_chain P : DPNormalizerOrbitPair.chain_of (point P) = c.
Proof. reflexivity. Qed.

Definition finite_category : CategoryFinite.finite_category :=
  @Build_finite_category object
    (fun P Q => DPNormalizerOrbitPair.pair_hom (point P) (point Q))
    (fun P => DPNormalizerOrbitPair.pair_identity (point P))
    (fun P Q U f g => DPNormalizerOrbitPair.pair_compose f g)
    (fun P Q f => DPNormalizerOrbitPair.pair_identity_left f)
    (fun P Q f => DPNormalizerOrbitPair.pair_identity_right f)
    (fun P Q U V f g h => DPNormalizerOrbitPair.pair_associative f g h).

Definition category : Category.category := fc_category finite_category.

Definition inclusion : functor category (DPNormalizerOrbitPair.pair_category F).
Proof.
refine (@Build_functor category (DPNormalizerOrbitPair.pair_category F)
  point (fun P Q f => f) _ _); reflexivity.
Defined.

Lemma inclusion_full (P Q : category)
    (f : hom (DPNormalizerOrbitPair.pair_category F) (point P) (point Q)) :
  exists g : hom category P Q, fmap inclusion g = f.
Proof. by exists f. Qed.

Lemma inclusion_faithful (P Q : category) : injective (@fmap _ _ inclusion P Q).
Proof. by move=> f g. Qed.

Definition forget : functor category (centric_orbit_category F) :=
  functor_comp inclusion (DPNormalizerOrbitPair.forget F).

Lemma forget_faithful (P Q : category) : injective (@fmap _ _ forget P Q).
Proof. exact: val_inj. Qed.

Lemma hom_extension_iff (P Q : object)
    (f : orbit_hom F (val (acting P)) (val (acting Q))) :
  DPNormalizerOrbitPair.compatible (A := point P) (B := point Q) f <->
  exists g : DPFusionSystem.arrow F (val (acting P)) (val (acting Q)),
    orbit_class g = f /\ DPChainNormalizerFusion.normalizer_extension c (val g).
Proof.
split; move=> [g [hg ha]]; exists g; split=> //.
- exact: (proj1 (@DPNormalizerChainSameExtension.same_extension_iff_join S F c
    (val (acting P)) (val (acting Q)) (val g))) ha.
- exact: (proj2 (@DPNormalizerChainSameExtension.same_extension_iff_join S F c
    (val (acting P)) (val (acting Q)) (val g))) ha.
Qed.

End Same.
End DPNormalizerOrbitSameChain.
