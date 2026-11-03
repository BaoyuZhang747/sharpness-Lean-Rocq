(** All-degree global comparison for the actual normalizer ordinary
    cohomology diagram, via the genuine pair and comma constructions. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits HomologicalModuleIso
  FusionSystems FusionOrbit FusionSaturation PrimeLocalRing PrimeLocalUniversal
  PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainIndexCategory
  GroupCohomologyOrbitCoefficient NormalizerOrdinaryCoefficient NormalizerOrdinaryPairHigherLimits
  NormalizerOrbitForgetHigherLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPLinkingChains DPNormalizerChainIndex
  DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryPairHigherLimits
  DPNormalizerOrbitForgetHigherLimits DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerOrdinaryHigherLimits.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.

Definition primes_inverted_higher_limit_iso (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n j : @isomorphism (module_category R)
    (derived_limit R (@representative_coefficient S F L r hr R A n) j)
    (derived_limit R (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j) :=
  module_iso_comp (@pair_higher_limit_iso S F L p hS sat r hr hp R localR A n j)
    (iso_symm (@forget_higher_limit_iso S F p hS sat R
      (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j)).

Definition field_higher_limit_iso (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n j :=
  primes_inverted_higher_limit_iso (pcharf_prime charp)
    (@DPFusionCentricAcyclicity.field_local p K charp) A n j.

Definition prime_local_algebra_higher_limit_iso (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n j :=
  primes_inverted_higher_limit_iso hp
    (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi) A n j.
End Comparison.
End DPNormalizerOrdinaryHigherLimits.
