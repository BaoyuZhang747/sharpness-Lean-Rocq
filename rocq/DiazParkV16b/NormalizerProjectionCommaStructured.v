(** The actual structured commas used by right Kan extension have precisely
    the checked normalizer-collection higher limits. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso CategoryIsomorphism CategoryIsomorphismAdjunction
  CategoryComma CategoryDerivedLimits CategoryDerivedAdjunction HomologicalModuleIso
  FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem NormalizerChainIndexCategory
  NormalizerOrbitPairCategory NormalizerOrbitPairProjection
  CategoryStructuredOpposite NormalizerProjectionCommaHigherLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPNormalizerChainIndex DPNormalizerProjectionCommaHigherLimits
  DiazParkHomologicalModuleIso.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaStructured.
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
Local Notation X := (opposite (costructured_category proj d)).
Local Notation Y := (structured_category (functor_op proj) d).
Local Notation chart := (@DPCategoryStructuredOpposite.comma_isomorphism _ _ proj d).

Definition pair_coefficient : module_codiagram R (DPNormalizerOrbitPair.pair_category F) :=
  functor_comp (functor_op (DPNormalizerOrbitPair.forget F)) M.

Definition structured_coefficient : module_diagram R Y :=
  functor_comp (structured_projection (functor_op proj) d) pair_coefficient.

Lemma structured_pullback_coefficient :
  functor_comp (category_iso_forward chart) structured_coefficient =
    @comma_coefficient S F d R M.
Proof.
apply (@functor_extensionality X (module_category R)
  (functor_comp (category_iso_forward chart) structured_coefficient)
  (@comma_coefficient S F d R M) (Logic.eq_refl _)); reflexivity.
Qed.

Definition structured_comma_derived_iso j : @isomorphism (module_category R)
  (derived_limit R structured_coefficient j)
  (derived_limit R (@comma_coefficient S F d R M) j).
Proof.
rewrite -structured_pullback_coefficient.
exact (nat_iso_component (derived_left_adjoint_nat_iso R (category_iso_adjunction chart) j)
  structured_coefficient).
Defined.

Definition structured_collection_derived_iso j : @isomorphism (module_category R)
  (derived_limit R structured_coefficient j)
  (derived_limit R (@collection_coefficient S F L p hS sat d R M) j) :=
  module_iso_comp (structured_comma_derived_iso j)
    (@comma_collection_derived_iso S F L p hS sat d R M j).
End Comparison.
End DPNormalizerProjectionCommaStructured.
