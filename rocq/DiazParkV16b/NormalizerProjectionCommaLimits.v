(** Actual compatible-family limits on the projection comma, normalized on
    every object of the literal local normalizer collection. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso CategoryIsomorphism CategoryIsomorphismAdjunction
  CategoryAdjunction CategoryComma CategoryModuleLimits CategoryModuleLimitFunctor
  CategoryLimitMaps HomologicalModuleIso HomologicalDiagramLimits
  FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects
  ChainNormalizerFusionOrbit NormalizerChainIndexCategory NormalizerOrbitPairCategory
  NormalizerOrbitPairProjection NormalizerOrbitSameChainCategory NormalizerOrbitSameChainEquivalence
  NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaInclusion
  NormalizerProjectionCommaReflection NormalizerProjectionCommaHigherLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPNormalizerChainIndex DPNormalizerProjectionCommaRepresentatives
  DPNormalizerProjectionCommaHigherLimits DiazParkHomologicalModuleIso.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaLimits.
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
Local Notation c := (@index_representative S F L p hS sat d).
Local Notation D := (DPNormalizerOrbitSameChain.category c).
Local Notation E := (DPChainNormalizerFusionOrbit.collection_category L c).
Local Notation incl := (@DPNormalizerProjectionCommaReflection.inclusion S F L p hS sat d).
Local Notation equiv := (@DPNormalizerOrbitSameChainEquivalence.collection_isomorphism S F L c p sat).
Local Notation Ccoef := (@comma_coefficient S F d R M).
Local Notation Dcoef := (@same_coefficient S F L p hS sat d R M).
Local Notation Ecoef := (@collection_coefficient S F L p hS sat d R M).
Local Notation Dpull := (functor_comp (functor_op incl) Ccoef).
Local Notation Epull := (functor_comp (functor_op (category_iso_forward equiv)) Dcoef).

Definition inclusion_coefficient_iso : @isomorphism
  (functor_category (opposite D) (module_category R)) Dpull Dcoef.
Proof.
apply (@nat_iso_of_components _ _ Dpull Dcoef (fun P => iso_refl _)).
move=> P Q f; rewrite compose_id_right compose_id_left; reflexivity.
Defined.

Definition collection_coefficient_iso : @isomorphism
  (functor_category (opposite E) (module_category R)) Epull Ecoef.
Proof.
apply (@nat_iso_of_components _ _ Epull Ecoef (fun P => iso_refl _)).
move=> P Q f; rewrite compose_id_right compose_id_left.
have hn := naturality (functor_equality_transformation
  (@collection_pullback_coefficient S F L p hS sat d R M)) f.
rewrite !functor_equality_component !equality_arrow_loop
  compose_id_right compose_id_left in hn.
exact hn.
Defined.

Definition comma_same_limit_iso : @isomorphism (module_category R)
  (module_limit_type Ccoef) (module_limit_type Dcoef) :=
  module_iso_comp
    (left_adjoint_limit_iso
      (@DPNormalizerProjectionCommaReflection.opposite_inclusion_adjunction S F L p hS sat d)
      Ccoef (module_limit Ccoef) (module_limit Dpull))
    (functor_iso (module_limit_functor R (opposite D)) inclusion_coefficient_iso).

Lemma comma_same_limit_component (v : module_limit_type Ccoef) (P : D) :
  module_limit_val (module_hom_fun (iso_hom comma_same_limit_iso) v) P =
    module_limit_val v (fobj incl P).
Proof.
change (module_limit_val (limit_action (iso_hom inclusion_coefficient_iso)
  (module_hom_fun (iso_hom (left_adjoint_limit_iso
    (@DPNormalizerProjectionCommaReflection.opposite_inclusion_adjunction S F L p hS sat d)
    Ccoef (module_limit Ccoef) (module_limit Dpull))) v)) P = module_limit_val v (fobj incl P)).
rewrite limit_action_coordinate.
have he := @left_adjoint_limit_iso_hom _ _ _ _ _
  (@DPNormalizerProjectionCommaReflection.opposite_inclusion_adjunction S F L p hS sat d)
  Ccoef (module_limit Ccoef) (module_limit Dpull).
rewrite he.
exact (congr1 (fun f => module_hom_fun f v)
  (@limit_restrict_map_fac _ _ _ (functor_op incl) Ccoef (module_limit Ccoef) (module_limit Dpull) P)).
Qed.

Definition same_collection_limit_iso : @isomorphism (module_category R)
  (module_limit_type Dcoef) (module_limit_type Ecoef) :=
  module_iso_comp
    (left_adjoint_limit_iso (adjunction_op (category_iso_adjunction (category_iso_symm equiv)))
      Dcoef (module_limit Dcoef) (module_limit Epull))
    (functor_iso (module_limit_functor R (opposite E)) collection_coefficient_iso).

Lemma same_collection_limit_component (v : module_limit_type Dcoef) (P : E) :
  module_limit_val (module_hom_fun (iso_hom same_collection_limit_iso) v) P =
    module_limit_val v (fobj (category_iso_forward equiv) P).
Proof.
change (module_limit_val (limit_action (iso_hom collection_coefficient_iso)
  (module_hom_fun (iso_hom (left_adjoint_limit_iso
    (adjunction_op (category_iso_adjunction (category_iso_symm equiv)))
    Dcoef (module_limit Dcoef) (module_limit Epull))) v)) P =
    module_limit_val v (fobj (category_iso_forward equiv) P)).
rewrite limit_action_coordinate.
have he := @left_adjoint_limit_iso_hom _ _ _ _ _
  (adjunction_op (category_iso_adjunction (category_iso_symm equiv)))
  Dcoef (module_limit Dcoef) (module_limit Epull).
rewrite he.
exact (congr1 (fun f => module_hom_fun f v)
  (@limit_restrict_map_fac _ _ _ (functor_op (category_iso_forward equiv))
    Dcoef (module_limit Dcoef) (module_limit Epull) P)).
Qed.

Definition comma_collection_limit_iso : @isomorphism (module_category R)
  (module_limit_type Ccoef) (module_limit_type Ecoef) :=
  module_iso_comp comma_same_limit_iso same_collection_limit_iso.

Theorem comma_collection_limit_component (v : module_limit_type Ccoef) (P : E) :
  module_limit_val (module_hom_fun (iso_hom comma_collection_limit_iso) v) P =
    module_limit_val v (fobj incl (fobj (category_iso_forward equiv) P)).
Proof.
change (module_limit_val (module_hom_fun (iso_hom same_collection_limit_iso)
  (module_hom_fun (iso_hom comma_same_limit_iso) v)) P =
    module_limit_val v (fobj incl (fobj (category_iso_forward equiv) P))).
rewrite same_collection_limit_component comma_same_limit_component; reflexivity.
Qed.
End Comparison.
End DPNormalizerProjectionCommaLimits.
