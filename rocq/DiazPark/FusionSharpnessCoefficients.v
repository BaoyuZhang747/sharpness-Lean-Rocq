(** Unconditional coefficient extensions of Diaz--Park sharpness. Values
    are arbitrary modules, and the algebra endpoint includes the zero ring. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionOrbit FusionSaturation FusionMackeyShape
  FusionSharpnessStatement FusionSharpnessTheorem
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  MackeyDiagramIdentities MackeyPrimeLocalFieldReduction MackeyPrimeLocalAlgebraReduction
  PrimeLocalRing PrimeLocalUniversal BarHigherLimitVanishing.
Import GRing.Theory DPFusionOrbit DPPrimeLocal DiazParkBarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPDiazParkCoefficients.
Section Coefficients.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Lemma prime_field_bar_acyclic
    (M : mackey_module [the comPzRingType of 'F_p] (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic (centric_inclusion F) M.
Proof.
  apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M)).
  exact (@DPDiazPark.diaz_park_theorem S F p pS sat [the fieldType of 'F_p] (pchar_Fp hp) M).
Qed.

Theorem prime_local_sharpness : DPFusionSharpness.sharpness
    [the comPzRingType of (DPPrimeLocal.type p : Type)] F.
Proof.
  exact (@DPMackeyPrimeLocalField.prime_local_centric_higher_of_prime_field
    S F p hp prime_field_bar_acyclic).
Qed.

Theorem prime_local_algebra_sharpness (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R}) : DPFusionSharpness.sharpness R F.
Proof.
  exact (@DPMackeyPrimeLocalAlgebra.prime_local_algebra_centric_higher_of_prime_field
    S F p hp R phi prime_field_bar_acyclic).
Qed.

Theorem primes_inverted_sharpness (R : comPzRingType)
    (localR : DPPrimeLocalUniversal.primes_inverted p R) : DPFusionSharpness.sharpness R F.
Proof. exact (prime_local_algebra_sharpness (DPPrimeLocalUniversal.canonical_map localR)). Qed.

Theorem inclusion_mackey_sharpness (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R})
    (M : mackey_pair R (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit R
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
  exact (@DPMackeyPrimeLocalAlgebra.prime_local_algebra_inclusion_higher_of_prime_field
    S F p hp R phi prime_field_bar_acyclic M hM).
Qed.
End Coefficients.
End DPDiazParkCoefficients.
