(** Unconditional positive derived-limit vanishing for the actual singular
    normalizer-space diagram, via its literal native ChainAut coefficient. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup zmodp all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleExactness CategoryDerivedLimits
  FusionSystems FusionSaturation PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem NormalizerChainIndexCategory NormalizerLinkingChainCategory
  NormalizerLinkingChainProjection NormalizerLinkingCommaCohomology NormalizerOrdinaryCoefficient
  NormalizerOrdinarySharpness TopologicalCategory SingularCochainReplacementEdge
  CategoryRealizationDecomposition CategoryRealizationCohomologyDiagram.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPTopological DPSingularReplacementEdge DPNormalizerChainIndex
  DPNormalizerLinkingChainCategory DPCategoryRealizationDecomposition DPCategoryRealizationCohomologyDiagram.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerLinkingRealizationSharpness.
Definition normalizer_space_diagram (Real : realType) (S : finGroupType)
    (F : DPFusionSystem.system S) (L : DPCentricLinking.system F) :=
  space_diagram Real (DPNormalizerLinkingChainProjection.projection L).
Section Comparison.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable n : nat.
Definition normalizer_native_coefficient_iso :
    @isomorphism (functor_category (opposite (index_category F)) (module_category R))
      (singular_cohomology_diagram Real A (normalizer_space_diagram Real L) n)
      (@DPNormalizerOrdinaryCoefficient.coefficient S F L R A n) :=
  diagram_iso_comp
    (@comparison_nat_iso Real R A (chain_category L) (index_category F)
      (DPNormalizerLinkingChainProjection.projection L) n)
    (@DPNormalizerLinkingCommaCohomology.canonical_comparison_nat_iso R A S F L n).
Theorem normalizer_native_coefficient_component d :
  component (iso_hom normalizer_native_coefficient_iso) d =
    module_hom_comp
      (component (iso_hom (@comparison_nat_iso Real R A (chain_category L) (index_category F)
        (DPNormalizerLinkingChainProjection.projection L) n)) d)
      (component (iso_hom (@DPNormalizerLinkingCommaCohomology.canonical_comparison_nat_iso R A S F L n)) d).
Proof. reflexivity. Qed.
Definition normalizer_native_higher_limit_iso j : @isomorphism (module_category R)
    (derived_limit R (singular_cohomology_diagram Real A (normalizer_space_diagram Real L) n) j)
    (derived_limit R (@DPNormalizerOrdinaryCoefficient.coefficient S F L R A n) j) :=
  functor_iso (derived_limit_functor R (opposite (index_category F)) j) normalizer_native_coefficient_iso.
Theorem normalizer_native_higher_limit_iso_hom j :
  iso_hom (normalizer_native_higher_limit_iso j) =
    derived_limit_map R (iso_hom normalizer_native_coefficient_iso) j.
Proof. reflexivity. Qed.
End Comparison.

Theorem field_positive_limits (Real : realType) (S : finGroupType) (F : DPFusionSystem.system S)
    (L : DPCentricLinking.system F) (p : nat) (hS : p.-group [set: S])
    (sat : DPFusionSaturation.saturated F p) (K : fieldType) (charp : p \in [pchar K]) (A : lmodType K) :
    singular_positive_limits_vanish Real A (normalizer_space_diagram Real L).
Proof.
move=> n j x.
pose e := @normalizer_native_higher_limit_iso Real [the comPzRingType of (K : Type)] A S F L n j.+1.
apply (module_iso_hom_injective (e := e)); rewrite module_hom_zero.
exact (@DPNormalizerOrdinarySharpness.field_higher_limits_zero S F L p hS sat K charp A n j
  (module_hom_fun (iso_hom e) x)).
Qed.
Theorem primes_inverted_positive_limits (Real : realType) (S : finGroupType) (F : DPFusionSystem.system S)
    (L : DPCentricLinking.system F) (p : nat) (hp : prime p) (hS : p.-group [set: S])
    (sat : DPFusionSaturation.saturated F p) (R : comPzRingType)
    (localR : DPPrimeLocalUniversal.primes_inverted p R) (A : lmodType R) :
    singular_positive_limits_vanish Real A (normalizer_space_diagram Real L).
Proof.
move=> n j x.
pose e := @normalizer_native_higher_limit_iso Real R A S F L n j.+1.
apply (module_iso_hom_injective (e := e)); rewrite module_hom_zero.
exact (@DPNormalizerOrdinarySharpness.primes_inverted_higher_limits_zero S F L p hS sat hp R localR A n j
  (module_hom_fun (iso_hom e) x)).
Qed.
End DPNormalizerLinkingRealizationSharpness.
