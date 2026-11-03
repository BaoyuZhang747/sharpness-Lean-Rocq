(** The v2.9 prime-local argument: finite-valued Nakayama reduction followed
    by the actual filtered direct-limit comparison for arbitrary values. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionOrbit FusionSaturation FusionMackeyShape FusionFiniteCategory
  FusionSharpnessStatement ModuleInfrastructure MackeySubquotients
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  MackeyDiagramIdentities MackeyPrimeLocalReduction MackeyPrimeLocalHigherReduction
  PrimeLocalTorsionDescent MackeyScalarRestriction FusionCentricAcyclicity
  PrimeLocalRing PrimeLocalUniversal BarHigherLimitVanishing.
From DiazParkV29 Require Import MainField CompositionFilteredMackey.
Import GRing.Theory DPFusionOrbit DPPrimeLocal DiazParkBarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV29DiazParkCoefficients.
Section Coefficients.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation Zp := [the comPzRingType of (DPPrimeLocal.type p : Type)].

Lemma prime_field_bar_acyclic
    (M : mackey_module [the comPzRingType of 'F_p] (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic (centric_inclusion F) M.
Proof.
apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M)).
exact (@DPV29DiazPark.diaz_park_theorem S F p pS sat [the fieldType of 'F_p] (pchar_Fp hp) M).
Qed.

Lemma prime_local_torsion_bar_acyclic
    (N : mackey_module Zp (DPFusionMackey.fusion_mackey_shape F))
    (hN : forall P (x : mackey_value N P), p%:R *: x = 0) :
    mackey_bar_acyclic (centric_inclusion F) N.
Proof.
exact (@DPPrimeLocalTorsion.torsion_acyclic_of_prime_field p hp
  (orbit_category F) (DPFusionMackey.fusion_mackey_shape F) N hN
  (centric_orbit_category F) (centric_inclusion F) prime_field_bar_acyclic).
Qed.

Lemma finite_prime_local_higher_limits
    (M : mackey_module Zp (DPFusionMackey.fusion_mackey_shape F))
    (hM : forall P, module_finitely_generated (mackey_value M P)) :
    forall n (q : derived_limit Zp (mackey_codiagram (centric_inclusion F) M) n.+1), q = 0.
Proof.
apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M)).
exact (@DPMackeyPrimeLocal.finite_prime_local_acyclic p hp (orbit_category F)
  (DPFusionFinite.centric_finite_category F) (DPFusionMackey.fusion_mackey_shape F)
  (DPMackeyPrimeLocalHigher.local_centric_finite_inclusion F)
  prime_local_torsion_bar_acyclic M hM).
Qed.

Theorem prime_local_sharpness : DPFusionSharpness.sharpness Zp F.
Proof.
move=> M n.
apply: DPFilteredLimitsMackey.centric_subfunctor_higher_limit_closure => N hN.
exact (@finite_prime_local_higher_limits (subfunctor_mackey N) hN n).
Qed.

Theorem prime_local_algebra_sharpness (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R}) : DPFusionSharpness.sharpness R F.
Proof.
move=> M n.
apply/(@DPMackeyScalarRestriction.restricted_mackey_higher_limit_zero_iff
  Zp R phi (orbit_category F) (DPFusionMackey.fusion_mackey_shape F) M
  (centric_orbit_category F) (centric_inclusion F) n.+1).
exact: prime_local_sharpness.
Qed.

End Coefficients.
End DPV29DiazParkCoefficients.

Print Assumptions DPV29DiazParkCoefficients.finite_prime_local_higher_limits.
Print Assumptions DPV29DiazParkCoefficients.prime_local_sharpness.
Print Assumptions DPV29DiazParkCoefficients.prime_local_algebra_sharpness.


