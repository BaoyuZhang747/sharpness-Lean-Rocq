(** The actual projection-comma reflection onto the fixed Sylow chain.
    Its universal arrows are constructed by the proved Sylow pointing and
    unique simultaneous-extension factorization. *)
From mathcomp Require Import all_boot all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryComma CategoryAdjunction FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainIndexCategory
  NormalizerOrbitPairCategory NormalizerOrbitPairProjection NormalizerOrbitSameChainCategory
  NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaPointing
  NormalizerProjectionCommaFactorization NormalizerProjectionCommaInclusion CategoryUniversalReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndex DPNormalizerProjectionCommaRepresentatives.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaReflection.
Section Reflection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable d : index_object F.
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).
Local Notation c := (@index_representative S F L p hS sat d).
Local Notation D := (DPNormalizerOrbitSameChain.category c).
Local Notation C := (costructured_category proj d).
Local Notation point := (@DPNormalizerOrbitSameChain.point S F c).
Local Notation acting := (@DPNormalizerOrbitPair.acting S F).

Definition inclusion : functor D C :=
  @DPNormalizerProjectionCommaInclusion.inclusion S F c d
    (@index_representative_class S F L p hS sat d).

Lemma pointing_exists (X : C) :
  exists B : D, exists u : DPNormalizerOrbitPair.pair_hom (costructured_source X) (point B),
    exists z : @isomorphism (DPFusionOrbit.centric_orbit_category F)
      (acting (costructured_source X)) (acting (point B)), iso_hom z = val u.
Proof.
have h := hom_relation (costructured_arrow X).
change (is_true (index_relation (chain_class (DPNormalizerOrbitPair.chain_of (costructured_source X))) d)) in h.
rewrite -(@index_representative_class S F L p hS sat d) class_relation in h.
have [B [hB [u [z hz]]]] :=
  @DPNormalizerProjectionCommaPointing.exists_pointing_of_subconjugate S F
    (costructured_source X) c p hS sat
    (@index_representative_automizer_sylow S F L p hS sat d) h.
have hN : val (acting B) \subset NormalizerChainNormalizer.DPNormalizerChain.normalizer c.
  rewrite -hB; exact: DPNormalizerOrbitPair.acting_normalizes.
pose T : D := Sub (acting B) hN.
have hT : point T = B.
  apply val_inj; change ((acting B, c) = val B); rewrite -hB.
  change (((val B).1, (val B).2) = val B).
  by case: (val B).
exists T; rewrite hT; exists u, z; exact hz.
Qed.

Definition pointing_data (X : C) :
  {B : D & {u : DPNormalizerOrbitPair.pair_hom (costructured_source X) (point B) &
    {z : @isomorphism (DPFusionOrbit.centric_orbit_category F)
      (acting (costructured_source X)) (acting (point B)) | iso_hom z = val u}}}.
Proof.
have [B hB] := cid (pointing_exists X).
have [u hu] := cid hB.
have [z hz] := cid hu.
exact (existT _ B (existT _ u (exist _ z hz))).
Defined.

Definition pointing_object (X : C) : D := projT1 (pointing_data X).
Definition pointing_arrow (X : C) :
  DPNormalizerOrbitPair.pair_hom (costructured_source X) (point (pointing_object X)) :=
  projT1 (projT2 (pointing_data X)).
Definition pointing_iso (X : C) : @isomorphism (DPFusionOrbit.centric_orbit_category F)
    (acting (costructured_source X)) (acting (point (pointing_object X))) :=
  proj1_sig (projT2 (projT2 (pointing_data X))).
Lemma pointing_iso_hom (X : C) : iso_hom (pointing_iso X) = val (pointing_arrow X).
Proof. exact (proj2_sig (projT2 (projT2 (pointing_data X)))). Qed.

Definition pointing_unit (X : C) : hom C X (fobj inclusion (pointing_object X)) :=
  @DPNormalizerProjectionCommaInclusion.to_comma_arrow S F c d
    (@index_representative_class S F L p hS sat d) X (pointing_object X) (pointing_arrow X).

Theorem pointing_universal (X : C) (B : D) (f : hom C X (fobj inclusion B)) :
  exists! g : hom D (pointing_object X) B,
    Category.compose (pointing_unit X) (fmap inclusion g) = f.
Proof.
have [g [hg hu]] := @DPNormalizerProjectionCommaFactorization.pointing_factorization S F
  (costructured_source X) c (pointing_object X) B (pointing_arrow X)
  (pointing_iso X) (pointing_iso_hom X) (costructured_map f).
exists g; split.
- apply costructured_hom_ext; exact hg.
- move=> g' h; apply: hu.
  exact (congr1 costructured_map h).
Qed.

Definition reflection : functor C D :=
  @DPCategoryUniversalReflection.reflection C D inclusion pointing_object pointing_unit pointing_universal.

Definition reflection_adjunction : adjunction reflection inclusion :=
  @DPCategoryUniversalReflection.reflection_adjunction C D inclusion pointing_object
    pointing_unit pointing_universal.

Theorem reflection_unit_component (X : C) :
  component (adj_unit reflection_adjunction) X = pointing_unit X.
Proof. reflexivity. Qed.

Definition opposite_inclusion_adjunction : adjunction (functor_op inclusion) (functor_op reflection) :=
  adjunction_op reflection_adjunction.
End Reflection.
End DPNormalizerProjectionCommaReflection.
