(** Changing chain representatives preserves the literal native
    restriction into the actual Ran coefficient. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryLimits CategoryLimitMaps CategoryComma CategoryStructured
  CategoryModules CategoryModuleLimits CategoryNaturalIso FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects
  NormalizerChainIndexCategory NormalizerOrbitPairCategory NormalizerOrbitPairProjection
  LinkingChainRestrictionMaps LinkingChainRestrictionOperations LinkingChainRestrictionUniqueness
  LinkingChainActingHom GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  NormalizerOrdinaryCoefficient NormalizerOrdinaryRepresentativeChange
  NormalizerOrdinaryChainComparison NormalizerOrdinaryRanMap NormalizerProjectionCommaStructured.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndex DPNormalizerOrbitPair
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations DPLinkingChainRestrictionUniqueness
  DPLinkingChainActingHom DPGroupCohomologyPullback DPGroupCohomologyOrbitCoefficient
  DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryRepresentativeChange
  DPNormalizerOrdinaryChainComparison DPNormalizerOrdinaryRanMap.

Module DPNormalizerOrdinaryRanRepresentativeChange.
Section Change.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables r s : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Hypothesis hs : forall d, chain_class (s d) = d.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation I := (index_category F).
Local Notation Mr := (@representative_coefficient S F L r hr R A n).
Local Notation Ms := (@representative_coefficient S F L s hs R A n).
Local Notation theta := (iso_hom (@representative_coefficient_iso S F L R A n r s hr hs)).
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).
Local Notation B := (@DPNormalizerProjectionCommaStructured.pair_coefficient S F R
  (centric_coefficient F A n)).

Lemma chain_comparison_change (c : chain F) :
    module_hom_comp (component theta (chain_class c))
      (iso_hom (@chain_comparison S F L s hs R A n c)) =
    iso_hom (@chain_comparison S F L r hr R A n c).
Proof.
rewrite representative_coefficient_iso_hom !chain_comparison_hom.
rewrite -pull_composition -composite_restriction; exact: chain_map_pull_unique.
Qed.

Theorem comparison_representative_change (d : I) :
    module_hom_comp (component theta d) (component (@comparison S F L s hs R A n) d) =
    component (@comparison S F L r hr R A n) d.
Proof.
apply (limit_hom_ext (module_limit (functor_comp (structured_projection (functor_op proj) d) B))).
move=> X.
change (compose (compose (component theta d) (component (@comparison S F L s hs R A n) d))
  (module_limit_projection (functor_comp (structured_projection (functor_op proj) d) B) X) =
  compose (component (@comparison S F L r hr R A n) d)
    (module_limit_projection (functor_comp (structured_projection (functor_op proj) d) B) X)).
have hsc := @comparison_coordinate S F L s hs R A n d X.
have hrc := @comparison_coordinate S F L r hr R A n d X.
change (compose (component (@comparison S F L s hs R A n) d)
  (module_limit_projection (functor_comp (structured_projection (functor_op proj) d) B) X) =
  compose (fmap Ms (structured_arrow X))
    (compose (iso_hom (@chain_comparison S F L s hs R A n (chain_of (structured_source X))))
      (pull A (acting_hom L (acting_normalizes (structured_source X))) n))) in hsc.
change (compose (component (@comparison S F L r hr R A n) d)
  (module_limit_projection (functor_comp (structured_projection (functor_op proj) d) B) X) =
  compose (fmap Mr (structured_arrow X))
    (compose (iso_hom (@chain_comparison S F L r hr R A n (chain_of (structured_source X))))
      (pull A (acting_hom L (acting_normalizes (structured_source X))) n))) in hrc.
rewrite compose_assoc hsc hrc -compose_assoc.
rewrite -(naturality theta (structured_arrow X)) compose_assoc.
have hc := chain_comparison_change (chain_of (structured_source X)).
change (compose (component theta (chain_class (chain_of (structured_source X))))
  (iso_hom (@chain_comparison S F L s hs R A n (chain_of (structured_source X)))) =
  iso_hom (@chain_comparison S F L r hr R A n (chain_of (structured_source X)))) in hc.
rewrite -[compose (component theta _) (compose _ _)]compose_assoc hc; reflexivity.
Qed.
End Change.
End DPNormalizerOrdinaryRanRepresentativeChange.
