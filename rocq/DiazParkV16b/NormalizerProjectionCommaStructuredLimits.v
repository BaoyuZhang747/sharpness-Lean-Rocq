(** Actual right-Kan values restrict to the local normalizer collection;
    every component is evaluation at the literal structured-comma point. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso CategoryIsomorphism CategoryIsomorphismAdjunction
  CategoryComma CategoryModuleLimits CategoryModuleLimitFunctor CategoryLimitMaps
  HomologicalModuleIso HomologicalDiagramLimits FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem ChainNormalizerFusionOrbit
  NormalizerChainIndexCategory NormalizerOrbitPairProjection NormalizerOrbitSameChainEquivalence
  NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaReflection
  CategoryStructuredOpposite NormalizerProjectionCommaHigherLimits
  NormalizerProjectionCommaStructured NormalizerProjectionCommaLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPNormalizerChainIndex DPNormalizerProjectionCommaRepresentatives
  DPNormalizerProjectionCommaHigherLimits DPNormalizerProjectionCommaStructured
  DPNormalizerProjectionCommaLimits DiazParkHomologicalModuleIso.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaStructuredLimits.
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
Local Notation C := (opposite (costructured_category proj d)).
Local Notation E := (DPChainNormalizerFusionOrbit.collection_category L c).
Local Notation incl := (@DPNormalizerProjectionCommaReflection.inclusion S F L p hS sat d).
Local Notation equiv := (@DPNormalizerOrbitSameChainEquivalence.collection_isomorphism S F L c p sat).
Local Notation chart := (@DPCategoryStructuredOpposite.comma_isomorphism _ _ proj d).
Local Notation Scoef := (@structured_coefficient S F d R M).
Local Notation Ccoef := (@comma_coefficient S F d R M).
Local Notation Ecoef := (@collection_coefficient S F L p hS sat d R M).
Local Notation Cpull := (functor_comp (category_iso_forward chart) Scoef).

Definition chart_coefficient_iso : @isomorphism
  (functor_category C (module_category R)) Cpull Ccoef.
Proof.
apply (@nat_iso_of_components _ _ Cpull Ccoef (fun X => iso_refl _)).
move=> X Y f; rewrite compose_id_right compose_id_left; reflexivity.
Defined.

Definition structured_comma_limit_iso : @isomorphism (module_category R)
  (module_limit_type Scoef) (module_limit_type Ccoef) :=
  module_iso_comp
    (left_adjoint_limit_iso (category_iso_adjunction chart)
      Scoef (module_limit Scoef) (module_limit Cpull))
    (functor_iso (module_limit_functor R C) chart_coefficient_iso).

Lemma structured_comma_limit_component (v : module_limit_type Scoef) (X : C) :
  module_limit_val (module_hom_fun (iso_hom structured_comma_limit_iso) v) X =
    module_limit_val v (fobj (category_iso_forward chart) X).
Proof.
change (module_limit_val (limit_action (iso_hom chart_coefficient_iso)
  (module_hom_fun (iso_hom (left_adjoint_limit_iso
    (category_iso_adjunction chart) Scoef (module_limit Scoef) (module_limit Cpull))) v)) X =
    module_limit_val v (fobj (category_iso_forward chart) X)).
rewrite limit_action_coordinate.
have he := @left_adjoint_limit_iso_hom _ _ _ _ _
  (category_iso_adjunction chart) Scoef (module_limit Scoef) (module_limit Cpull).
rewrite he.
exact (congr1 (fun f => module_hom_fun f v)
  (@limit_restrict_map_fac _ _ _ (category_iso_forward chart)
    Scoef (module_limit Scoef) (module_limit Cpull) X)).
Qed.

Definition collection_point (P : E) : structured_category (functor_op proj) d :=
  fobj (category_iso_forward chart) (fobj incl (fobj (category_iso_forward equiv) P)).

Definition structured_collection_limit_iso : @isomorphism (module_category R)
  (module_limit_type Scoef) (module_limit_type Ecoef) :=
  module_iso_comp structured_comma_limit_iso
    (@comma_collection_limit_iso S F L p hS sat d R M).

Theorem structured_collection_limit_component (v : module_limit_type Scoef) (P : E) :
  module_limit_val (module_hom_fun (iso_hom structured_collection_limit_iso) v) P =
    module_limit_val v (collection_point P).
Proof.
change (module_limit_val (module_hom_fun (iso_hom
  (@comma_collection_limit_iso S F L p hS sat d R M))
  (module_hom_fun (iso_hom structured_comma_limit_iso) v)) P =
    module_limit_val v (collection_point P)).
rewrite comma_collection_limit_component structured_comma_limit_component; reflexivity.
Qed.
End Comparison.
End DPNormalizerProjectionCommaStructuredLimits.
