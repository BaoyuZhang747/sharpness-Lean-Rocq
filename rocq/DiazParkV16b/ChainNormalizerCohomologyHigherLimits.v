(** Positive higher limits of the actual ambient ordinary-cohomology
    coefficient vanish on the literal local normalizer collection. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryDerivedLimits HomologicalModuleIso BarHigherLimitVanishing
  FusionSystems FusionOrbit FusionSaturation PrimeLocalRing PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainNormalizer NormalizerChainEmbedding ChainNormalizerFusionModel
  ChainNormalizerFusionOrbit ChainNormalizerFusionSaturation ChainNormalizerBottomCollection
  ChainNormalizerFusionCollection ChainNormalizerCohomologyCoefficient
  GroupCohomologyOrbitCoefficient GroupCohomologySharpness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainEmbedding DPChainNormalizerFusionModel DPChainNormalizerFusionOrbit
  DPChainNormalizerFusionCollection DPChainNormalizerCohomologyCoefficient
  DiazParkHomologicalModuleIso DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPChainNormalizerCohomologyHigherLimits.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable c : chain F.
Variable hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c).
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Definition ambient_collection_derived_iso j : @isomorphism (module_category R)
    (derived_limit R (DPGroupCohomologyOrbitCoefficient.centric_coefficient
      (local_system L c) A n) j)
    (derived_limit R (@ambient_coefficient S F L c p sat R A n) j) :=
  module_iso_comp (@sylow_collection_derived_iso S F L p hS sat c hs R
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient (local_system L c) A n) j)
    (functor_iso (derived_limit_functor R (opposite (collection_category L c)) j)
      (@collection_coefficient_nat_iso S F L c p sat R A n)).

End Comparison.

Section Vanishing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable c : chain F.
Variable hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c).

Theorem field_ambient_collection_higher_zero
    (K : fieldType) (charp : p \in [pchar K]) (A : lmodType K) (n j : nat) :
  forall q : derived_limit K (@ambient_coefficient S F L c p sat K A n) j.+1, q = 0.
Proof.
apply/(module_iso_zero_iff (@ambient_collection_derived_iso S F L p hS sat c hs K A n j.+1)).
exact (@DPGroupCohomologySharpness.field_higher_limits_zero _ (local_system L c) p
  (@DPChainNormalizerBottomCollection.normalizer_carrier_pgroup S F c p hS)
  (@DPChainNormalizerFusionSaturation.local_saturated S F L c p hs) K charp A n j).
Qed.

Theorem prime_local_algebra_ambient_collection_higher_zero
    (hp : prime p) (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) (n j : nat) :
  forall q : derived_limit R (@ambient_coefficient S F L c p sat R A n) j.+1, q = 0.
Proof.
apply/(module_iso_zero_iff (@ambient_collection_derived_iso S F L p hS sat c hs R A n j.+1)).
exact (@DPGroupCohomologySharpness.prime_local_algebra_higher_limits_zero _ (local_system L c) p hp
  (@DPChainNormalizerBottomCollection.normalizer_carrier_pgroup S F c p hS)
  (@DPChainNormalizerFusionSaturation.local_saturated S F L c p hs) R phi A n j).
Qed.

Theorem primes_inverted_ambient_collection_higher_zero
    (hp : prime p) (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) (n j : nat) :
  forall q : derived_limit R (@ambient_coefficient S F L c p sat R A n) j.+1, q = 0.
Proof.
exact (@prime_local_algebra_ambient_collection_higher_zero hp R
  (DPPrimeLocalUniversal.canonical_map localR) A n j).
Qed.

End Vanishing.

Theorem field_representative_ambient_collection_higher_zero
    (S : finGroupType) (F : DPFusionSystem.system S) (L : DPCentricLinking.system F)
    (p : nat) (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (c : chain F) (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) (n j : nat) :
  forall q : derived_limit K
    (@ambient_coefficient S F L (@sylow_representative S F L p hS sat c) p sat K A n)
    j.+1, q = 0.
Proof.
exact (@field_ambient_collection_higher_zero S F L p hS sat _
  (@representative_sylow S F L p hS sat c) K charp A n j).
Qed.

Theorem prime_local_algebra_representative_ambient_collection_higher_zero
    (S : finGroupType) (F : DPFusionSystem.system S) (L : DPCentricLinking.system F)
    (p : nat) (hp : prime p) (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (c : chain F) (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) (n j : nat) :
  forall q : derived_limit R
    (@ambient_coefficient S F L (@sylow_representative S F L p hS sat c) p sat R A n)
    j.+1, q = 0.
Proof.
exact (@prime_local_algebra_ambient_collection_higher_zero S F L p hS sat _
  (@representative_sylow S F L p hS sat c) hp R phi A n j).
Qed.

End DPChainNormalizerCohomologyHigherLimits.
