(** The explicit normalizer restriction transposes through the actual
    right Kan adjunction. Every comma component remains a native pull. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryComma CategoryStructured CategoryModules
  CategoryModuleLimits CategoryModuleRightKan FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory NormalizerOrbitPairCategory NormalizerOrbitPairProjection
  LinkingChainActingHom GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  NormalizerOrdinaryCoefficient NormalizerOrdinaryChainComparison
  NormalizerOrdinaryPairRestriction CategoryModuleRanTranspose
  NormalizerProjectionCommaStructured NormalizerProjectionCommaGroupLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndex DPNormalizerOrbitPair
  DPLinkingChainActingHom DPGroupCohomologyPullback DPGroupCohomologyOrbitCoefficient
  DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryChainComparison
  DPNormalizerOrdinaryPairRestriction DPNormalizerProjectionCommaGroupLimit.

Module DPNormalizerOrdinaryRanMap.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation I := (index_category F).
Local Notation E := (pair_category F).
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).
Local Notation M := (@representative_coefficient S F L r hr R A n).
Local Notation B := (@DPNormalizerProjectionCommaStructured.pair_coefficient S F R
  (centric_coefficient F A n)).

Definition comparison : nat_trans M (@native_ran_coefficient S F R A n) :=
  DPCategoryModuleRanTranspose.transpose
    (@pair_native_restriction S F L r hr R A n).

Theorem comparison_coordinate (d : I) (X : structured_category (functor_op proj) d) :
    module_hom_comp (component comparison d)
      (module_limit_projection (functor_comp (structured_projection (functor_op proj) d) B) X) =
    module_hom_comp (fmap M (structured_arrow X))
      (module_hom_comp (iso_hom (@chain_comparison S F L r hr R A n
        (chain_of (structured_source X))))
        (pull A (acting_hom L (acting_normalizes (structured_source X))) n)).
Proof. exact: DPCategoryModuleRanTranspose.transpose_coordinate. Qed.

Theorem comparison_pair_coordinate (X : E) :
    module_hom_comp (component comparison (fobj proj X))
      (module_limit_projection
        (functor_comp (structured_projection (functor_op proj) (fobj proj X)) B)
        (structured_identity_point (functor_op proj) X)) =
    module_hom_comp (iso_hom (@chain_comparison S F L r hr R A n (chain_of X)))
      (pull A (acting_hom L (acting_normalizes X)) n).
Proof.
exact (@DPCategoryModuleRanTranspose.transpose_identity_coordinate R
  (opposite E) (opposite I) (functor_op proj) M B
  (@pair_native_restriction S F L r hr R A n) X).
Qed.
End Comparison.
End DPNormalizerOrdinaryRanMap.
