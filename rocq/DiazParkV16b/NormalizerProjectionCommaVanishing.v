(** Positive higher limits vanish on the actual right-Kan comma categories
    for native ordinary cohomology. No local comparison hypothesis remains. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  BarHigherLimitVanishing FusionSystems FusionOrbit FusionSaturation
  PrimeLocalRing PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem NormalizerChainIndexCategory
  NormalizerOrbitPairCategory NormalizerOrbitPairProjection GroupCohomologyOrbitCoefficient
  ChainNormalizerCohomologyHigherLimits NormalizerProjectionCommaRepresentatives
  NormalizerProjectionCommaHigherLimits NormalizerProjectionCommaStructured
  CategoryRanAcyclicComparisonResolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPNormalizerChainIndex DPNormalizerProjectionCommaRepresentatives
  DPNormalizerProjectionCommaHigherLimits DPNormalizerProjectionCommaStructured
  DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerProjectionCommaVanishing.
Section Vanishing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).

Theorem field_structured_higher_zero (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n (d : index_object F) j :
  forall q : derived_limit K (@structured_coefficient S F d K
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)) j.+1, q = 0.
Proof.
apply/(module_iso_zero_iff (@structured_collection_derived_iso S F L p hS sat d K
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j.+1)).
exact (@DPChainNormalizerCohomologyHigherLimits.field_ambient_collection_higher_zero
  S F L p hS sat (@index_representative S F L p hS sat d)
  (@index_representative_sylow S F L p hS sat d) K charp A n j).
Qed.

Theorem prime_local_algebra_structured_higher_zero (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n (d : index_object F) j :
  forall q : derived_limit R (@structured_coefficient S F d R
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)) j.+1, q = 0.
Proof.
apply/(module_iso_zero_iff (@structured_collection_derived_iso S F L p hS sat d R
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j.+1)).
exact (@DPChainNormalizerCohomologyHigherLimits.prime_local_algebra_ambient_collection_higher_zero
  S F L p hS sat (@index_representative S F L p hS sat d)
  (@index_representative_sylow S F L p hS sat d) hp R phi A n j).
Qed.

Theorem primes_inverted_structured_higher_zero (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n (d : index_object F) j :
  forall q : derived_limit R (@structured_coefficient S F d R
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)) j.+1, q = 0.
Proof. exact (@prime_local_algebra_structured_higher_zero hp R
  (DPPrimeLocalUniversal.canonical_map localR) A n d j). Qed.

Theorem field_ran_comma_acyclic (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :
  ran_comma_positive_acyclic K (functor_op proj)
    (@pair_coefficient S F K (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)).
Proof. exact (fun d j => @field_structured_higher_zero K charp A n d j). Qed.

Theorem prime_local_algebra_ran_comma_acyclic (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n :
  ran_comma_positive_acyclic R (functor_op proj)
    (@pair_coefficient S F R (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)).
Proof. exact (fun d j => @prime_local_algebra_structured_higher_zero hp R phi A n d j). Qed.

Theorem primes_inverted_ran_comma_acyclic (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n :
  ran_comma_positive_acyclic R (functor_op proj)
    (@pair_coefficient S F R (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)).
Proof. exact (fun d j => @primes_inverted_structured_higher_zero hp R localR A n d j). Qed.
End Vanishing.
End DPNormalizerProjectionCommaVanishing.
