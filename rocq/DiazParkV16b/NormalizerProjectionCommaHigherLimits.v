(** Actual projection-comma higher limits restrict to the genuine local
    normalizer collection, in every degree and for arbitrary coefficients. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso CategoryIsomorphism CategoryIsomorphismAdjunction
  CategoryAdjunction CategoryComma CategoryDerivedLimits CategoryDerivedAdjunction
  HomologicalModuleIso FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects
  ChainNormalizerFusionOrbit NormalizerChainIndexCategory NormalizerOrbitPairCategory
  NormalizerOrbitPairProjection NormalizerOrbitSameChainCategory NormalizerOrbitSameChainEquivalence
  NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaInclusion
  NormalizerProjectionCommaReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndex DPNormalizerProjectionCommaRepresentatives
  DiazParkHomologicalModuleIso.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaHigherLimits.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable d : index_object F.
Variable R : pzRingType.
Variable M : module_codiagram R (DPFusionOrbit.centric_orbit_category F).
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).
Local Notation c := (@index_representative S F L p hS sat d).
Local Notation C := (costructured_category proj d).
Local Notation D := (DPNormalizerOrbitSameChain.category c).
Local Notation E := (DPChainNormalizerFusionOrbit.collection_category L c).
Local Notation incl := (@DPNormalizerProjectionCommaReflection.inclusion S F L p hS sat d).
Local Notation equiv := (@DPNormalizerOrbitSameChainEquivalence.collection_isomorphism S F L c p sat).

Definition comma_coefficient : module_codiagram R C :=
  functor_comp (functor_op (costructured_projection proj d))
    (functor_comp (functor_op (DPNormalizerOrbitPair.forget F)) M).

Definition same_coefficient : module_codiagram R D :=
  functor_comp (functor_op (DPNormalizerOrbitSameChain.forget c)) M.

Definition collection_coefficient : module_codiagram R E :=
  functor_comp (functor_op (@DPChainNormalizerFusionOrbit.collection_ambient_functor S F L c p sat)) M.

Lemma inclusion_coefficient :
  functor_comp (functor_op incl) comma_coefficient = same_coefficient.
Proof.
apply (@functor_extensionality (opposite D) (module_category R)
  (functor_comp (functor_op incl) comma_coefficient) same_coefficient (Logic.eq_refl _)).
reflexivity.
Qed.

Definition comma_same_derived_iso j : @isomorphism (module_category R)
  (derived_limit R comma_coefficient j) (derived_limit R same_coefficient j).
Proof.
rewrite -inclusion_coefficient.
exact (nat_iso_component (derived_left_adjoint_nat_iso R
  (@DPNormalizerProjectionCommaReflection.opposite_inclusion_adjunction S F L p hS sat d) j)
  comma_coefficient).
Defined.

Lemma collection_pullback_coefficient :
  functor_comp (functor_op (category_iso_forward equiv)) same_coefficient = collection_coefficient.
Proof.
have h := @DPNormalizerOrbitSameChainEquivalence.collection_forward_forget S F L c p sat.
have h' := congr1 (fun J => functor_comp (functor_op J) M) h.
rewrite /collection_coefficient -h'.
apply (@functor_extensionality (opposite E) (module_category R)
  (functor_comp (functor_op (category_iso_forward equiv)) same_coefficient)
  (functor_comp (functor_op (functor_comp (category_iso_forward equiv)
    (DPNormalizerOrbitSameChain.forget c))) M) (Logic.eq_refl _)).
reflexivity.
Qed.

Definition same_collection_derived_iso j : @isomorphism (module_category R)
  (derived_limit R same_coefficient j) (derived_limit R collection_coefficient j).
Proof.
rewrite -collection_pullback_coefficient.
exact (nat_iso_component (derived_left_adjoint_nat_iso R
  (adjunction_op (category_iso_adjunction (category_iso_symm equiv))) j) same_coefficient).
Defined.

Definition comma_collection_derived_iso j : @isomorphism (module_category R)
  (derived_limit R comma_coefficient j) (derived_limit R collection_coefficient j) :=
  module_iso_comp (comma_same_derived_iso j) (same_collection_derived_iso j).
End Comparison.
End DPNormalizerProjectionCommaHigherLimits.
