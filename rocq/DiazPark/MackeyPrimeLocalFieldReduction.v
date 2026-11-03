From mathcomp Require Import all_boot all_algebra all_fingroup boolp rat zmodp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge
  MackeyBarReduction MackeyPrimeLocalHigherReduction PrimeLocalRing
  PrimeLocalTorsionDescent FusionSystems FusionOrbit FusionMackeyShape
  BarComplex BarHigherLimitVanishing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPFusionOrbit DPMackeyPrimeLocalHigher
  DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Module DPMackeyPrimeLocalField.
Section FieldReduction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation R := [the comPzRingType of (DPPrimeLocal.type p : Type)].
Local Notation K := [the comPzRingType of 'F_p].

Hypothesis field_acyclic : forall N : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
  mackey_bar_acyclic (centric_inclusion F) N.

Theorem prime_local_centric_bar_of_prime_field
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic (centric_inclusion F) M.
Proof.
apply: (@prime_local_centric_bar_of_torsion S F p hp) => N hN.
exact (@DPPrimeLocalTorsion.torsion_acyclic_of_prime_field p hp
  (orbit_category F) (DPFusionMackey.fusion_mackey_shape F) N hN
  (centric_orbit_category F) (centric_inclusion F) field_acyclic).
Qed.

Theorem prime_local_centric_higher_of_prime_field
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) :
    forall n (q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n.+1), q = 0.
Proof.
apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M)).
exact: prime_local_centric_bar_of_prime_field.
Qed.

Theorem prime_local_inclusion_higher_of_prime_field
    (M : mackey_pair R (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit R
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
apply: (@prime_local_inclusion_higher_of_torsion S F p hp _ M hM) => N hN.
exact (@DPPrimeLocalTorsion.torsion_acyclic_of_prime_field p hp
  (orbit_category F) (DPFusionMackey.fusion_mackey_shape F) N hN
  (centric_orbit_category F) (centric_inclusion F) field_acyclic).
Qed.

End FieldReduction.
End DPMackeyPrimeLocalField.
