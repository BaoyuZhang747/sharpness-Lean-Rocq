(** Public algebraic statements for the revised v2.8 manuscript through Route B.
    The field corollary below is deduced from the prime-local theorem
    through the actual all-degree scalar-restriction isomorphism. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp vector boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryModules CategoryDerivedLimits
  FusionSystems FusionSaturation FusionOrbit FusionMackeyShape FusionCentricAcyclicity
  FusionMackeyFullBridge MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge
  MackeyBarReduction MackeyDiagramIdentities MackeyScalarRestriction PrimeLocalRing PrimeLocalUniversal.
From DiazParkV16b Require Import MackeyFixedDegreeClosure.
From DiazParkV28 Require Import FusionSharpnessCoefficientsRouteB.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPPrimeLocal.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV28DiazParkManuscript.

(** This is actual finite-dimensionality of the existing value module:
    a finite-dimensional vector-space coordinate axiom, without changing
    its carrier or its linear operations. *)
Definition finite_dimensional_values (S : finGroupType) (F : DPFusionSystem.system S)
    (K : fieldType) (M : mackey_pair K (orbit_category F)) : Prop :=
  forall P : {group S}, exists d : nat, inhabited (Vector.axiom d (pair_value M P)).

Section MainTheorems.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation Zp := [the comPzRingType of (DPPrimeLocal.type p : Type)].

Theorem prime_local_main
    (M : mackey_pair Zp (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit Zp
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
rewrite -(DPMackeyFixedDegree.inclusion_centric_codiagram hM).
exact (@DPV28DiazParkCoefficients.prime_local_sharpness S F p hp pS sat
  (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

(** Arbitrary commutative Z_(p)-algebras, including the zero ring, are
    handled by restriction of scalars, not by a finite-dimensional model. *)
Theorem algebra_sharpness_from_prime_local (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R})
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) n :
    forall q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n.+1, q = 0.
Proof.
apply/(@DPMackeyScalarRestriction.restricted_mackey_higher_limit_zero_iff
  Zp R phi (orbit_category F) (DPFusionMackey.fusion_mackey_shape F) M
  (centric_orbit_category F) (centric_inclusion F) n.+1).
pose N := @DPMackeyScalarRestriction.restricted_mackey Zp R phi (orbit_category F)
  (DPFusionMackey.fusion_mackey_shape F) M.
change (forall q : derived_limit Zp (mackey_codiagram (centric_inclusion F) N) n.+1, q = 0).
rewrite native_pair_codiagram.
exact (@prime_local_main (pair_of_mackey N)
  (@DPFusionMackeyFullBridge.full_inclusion_mackey S F Zp N) n).
Qed.

Theorem field_corollary_from_prime_local (K : fieldType) (charp : p \in [pchar K])
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) n :
    forall q : derived_limit K (mackey_codiagram (centric_inclusion F) M) n.+1, q = 0.
Proof.
exact (@algebra_sharpness_from_prime_local [the comPzRingType of (K : Type)]
  (DPPrimeLocalUniversal.canonical_map (@DPFusionCentricAcyclicity.field_local p K charp)) M n).
Qed.

Theorem field_corollary (K : fieldType) (charp : p \in [pchar K])
    (M : mackey_pair K (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit K
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
rewrite -(DPMackeyFixedDegree.inclusion_centric_codiagram hM).
exact (@field_corollary_from_prime_local K charp (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

Theorem diaz_park_conjecture
    (M : mackey_pair [the comPzRingType of 'F_p] (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (finite_values : finite_dimensional_values M) :
    forall n (q : derived_limit [the pzRingType of 'F_p]
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
exact (@field_corollary [the fieldType of 'F_p] (pchar_Fp hp) M hM).
Qed.

Theorem prime_local_main_positive
    (M : mackey_pair Zp (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (i : nat) (hi : (0 < i)%N) :
    forall q : derived_limit Zp
      (pair_codiagram (pair_restrict M (centric_inclusion F))) i, q = 0.
Proof. case: i hi => [|n] // _; exact (@prime_local_main M hM n). Qed.

Theorem field_corollary_positive (K : fieldType) (charp : p \in [pchar K])
    (M : mackey_pair K (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (i : nat) (hi : (0 < i)%N) :
    forall q : derived_limit K
      (pair_codiagram (pair_restrict M (centric_inclusion F))) i, q = 0.
Proof. case: i hi => [|n] // _; exact (@field_corollary K charp M hM n). Qed.

Theorem diaz_park_conjecture_positive
    (M : mackey_pair [the comPzRingType of 'F_p] (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (finite_values : finite_dimensional_values M) (i : nat) (hi : (0 < i)%N) :
    forall q : derived_limit [the pzRingType of 'F_p]
      (pair_codiagram (pair_restrict M (centric_inclusion F))) i, q = 0.
Proof. case: i hi => [|n] // _; exact (@diaz_park_conjecture M hM finite_values n). Qed.
End MainTheorems.

End DPV28DiazParkManuscript.
