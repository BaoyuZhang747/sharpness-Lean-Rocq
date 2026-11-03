(** Higher-limit vanishing for the actual ordinary-cohomology coefficient.
    All transfer and Mackey data are constructed; only the mathematical
    hypotheses on the fusion system and coefficient ring occur below. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionOrbit FusionSaturation FusionSharpnessTheorem
  FusionSharpnessCoefficients PrimeLocalRing PrimeLocalUniversal.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient GroupCohomologyMackeyNative.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPGroupCohomologyOrbitCoefficient DPGroupCohomologyMackeyNative.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPGroupCohomologySharpness.

Theorem field_higher_limits_zero (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (K : fieldType) (charp : p \in [pchar K]) (A : lmodType K) (n j : nat) :
  forall q : derived_limit K (centric_coefficient F A n) j.+1, q = 0.
Proof.
have e : MackeyBarReduction.mackey_codiagram (DPFusionOrbit.centric_inclusion F)
  (native_cohomology_mackey F A n) = centric_coefficient F A n :=
  native_mackey_centric_diagram F A n.
rewrite -e.
exact (@DPDiazPark.diaz_park_theorem S F p pS sat K charp
  (native_cohomology_mackey F A n) j).
Qed.

Theorem prime_field_higher_limits_zero (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (hp : prime p) (pS : p.-group [set: S])
    (sat : DPFusionSaturation.saturated F p)
    (A : lmodType [the fieldType of 'F_p]) (n j : nat) :
  forall q : derived_limit [the fieldType of 'F_p] (centric_coefficient F A n) j.+1, q = 0.
Proof. exact (@field_higher_limits_zero S F p pS sat _ (pchar_Fp hp) A n j). Qed.

Theorem prime_local_algebra_higher_limits_zero
    (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (hp : prime p) (pS : p.-group [set: S])
    (sat : DPFusionSaturation.saturated F p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) (n j : nat) :
  forall q : derived_limit R (centric_coefficient F A n) j.+1, q = 0.
Proof.
have e : MackeyBarReduction.mackey_codiagram (DPFusionOrbit.centric_inclusion F)
  (native_cohomology_mackey F A n) = centric_coefficient F A n :=
  native_mackey_centric_diagram F A n.
rewrite -e.
exact (@DPDiazParkCoefficients.prime_local_algebra_sharpness S F p hp pS sat R phi
  (native_cohomology_mackey F A n) j).
Qed.

Theorem primes_inverted_higher_limits_zero
    (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (hp : prime p) (pS : p.-group [set: S])
    (sat : DPFusionSaturation.saturated F p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) (n j : nat) :
  forall q : derived_limit R (centric_coefficient F A n) j.+1, q = 0.
Proof.
exact (@prime_local_algebra_higher_limits_zero S F p hp pS sat R
  (DPPrimeLocalUniversal.canonical_map localR) A n j).
Qed.

End DPGroupCohomologySharpness.
