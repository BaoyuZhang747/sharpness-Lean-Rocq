(** Native all-degree normalizer-to-pair comparison. The right Kan
    acyclicity and coefficient comparison are both constructed. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryNaturalIso
  CategoryDerivedLimits CategoryModuleLimits CategoryModuleLimitFunctor CategoryModuleRightKanLimits
  HomologicalModuleIso FusionSystems FusionOrbit FusionSaturation
  PrimeLocalRing PrimeLocalUniversal PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainIndexCategory
  NormalizerOrbitPairCategory NormalizerOrbitPairProjection GroupCohomologyOrbitCoefficient
  NormalizerOrdinaryCoefficient NormalizerOrdinaryRanIso NormalizerProjectionCommaStructured
  NormalizerProjectionCommaGroupLimit NormalizerProjectionCommaVanishing CategoryRanAcyclicComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPLinkingChains DPNormalizerChainIndex
  DPNormalizerOrdinaryCoefficient DPNormalizerProjectionCommaStructured
  DPNormalizerProjectionCommaGroupLimit DPNormalizerProjectionCommaVanishing
  DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerOrdinaryPairHigherLimits.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variable hp : prime p.
Variable R : comPzRingType.
Variable localR : DPPrimeLocalUniversal.primes_inverted p R.
Variable A : lmodType R.
Variable n : nat.
Local Notation I := (opposite (index_category F)).
Local Notation M := (@representative_coefficient S F L r hr R A n).
Local Notation B := (@pair_coefficient S F R
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)).
Local Notation proj := (functor_op (DPNormalizerOrbitPairProjection.projection F)).
Local Notation e := (@DPNormalizerOrdinaryRanIso.primes_inverted_ran_iso
  S F L p hS sat r hr hp R localR A n).
Local Notation ac := (@primes_inverted_ran_comma_acyclic S F L p hS sat hp R localR A n).

Definition pair_higher_limit_iso j : @isomorphism (module_category R)
    (derived_limit R M j) (derived_limit R B j) :=
  module_iso_comp (functor_iso (derived_limit_functor R I j) e)
    (ran_acyclic_higher_limit_iso R proj ac j).

Definition pair_limit_iso : @isomorphism (module_category R)
    (module_limit_type M) (module_limit_type B) :=
  module_iso_comp (functor_iso (module_limit_functor R I) e)
    (module_ran_limit_iso R proj B).

Theorem pair_higher_limit_iso_hom j : iso_hom (pair_higher_limit_iso j) =
    module_hom_comp (derived_limit_map R (iso_hom e) j)
      (iso_hom (ran_acyclic_higher_limit_iso R proj ac j)).
Proof. reflexivity. Qed.
End Comparison.
End DPNormalizerOrdinaryPairHigherLimits.
