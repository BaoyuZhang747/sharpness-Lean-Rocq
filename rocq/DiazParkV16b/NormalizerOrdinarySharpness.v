(** Unconditional positive higher-limit vanishing for the actual native
    normalizer ordinary-cohomology coefficient on the genuine quotient index. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits BarHigherLimitVanishing
  FusionSystems FusionOrbit FusionSaturation PrimeLocalRing PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem NormalizerOrdinaryCoefficient
  NormalizerOrdinaryHigherLimits GroupCohomologySharpness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPNormalizerOrdinaryCoefficient
  DPNormalizerOrdinaryHigherLimits DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerOrdinarySharpness.
Section Sharpness.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Local Notation r := (@canonical_representative S F).
Local Notation hr := (@canonical_representative_class S F).

Theorem primes_inverted_higher_limits_zero (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n j :
    forall z : derived_limit R (@coefficient S F L R A n) j.+1, z = 0.
Proof.
apply/(module_iso_zero_iff
  (@primes_inverted_higher_limit_iso S F L p hS sat r hr hp R localR A n j.+1)).
exact (@DPGroupCohomologySharpness.primes_inverted_higher_limits_zero S F p hp hS sat R localR A n j).
Qed.

Theorem field_higher_limits_zero (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n j :
    forall z : derived_limit K (@coefficient S F L K A n) j.+1, z = 0.
Proof.
apply/(module_iso_zero_iff
  (@field_higher_limit_iso S F L p hS sat r hr K charp A n j.+1)).
exact (@DPGroupCohomologySharpness.field_higher_limits_zero S F p hS sat K charp A n j).
Qed.

Theorem prime_field_higher_limits_zero (hp : prime p)
    (A : lmodType [the fieldType of 'F_p]) n j :
    forall z : derived_limit [the fieldType of 'F_p]
      (@coefficient S F L [the fieldType of 'F_p] A n) j.+1, z = 0.
Proof. exact (@field_higher_limits_zero _ (pchar_Fp hp) A n j). Qed.

Theorem prime_local_algebra_higher_limits_zero (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n j :
    forall z : derived_limit R (@coefficient S F L R A n) j.+1, z = 0.
Proof.
apply/(module_iso_zero_iff
  (@prime_local_algebra_higher_limit_iso S F L p hS sat r hr hp R phi A n j.+1)).
exact (@DPGroupCohomologySharpness.prime_local_algebra_higher_limits_zero S F p hp hS sat R phi A n j).
Qed.
End Sharpness.
End DPNormalizerOrdinarySharpness.
