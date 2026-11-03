(** Arbitrary commutative Z_(p)-algebras and arbitrary module values.
    The only sharpness premise is the corresponding theorem over F_p. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp rat zmodp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge
  MackeyBarReduction MackeyPrimeLocalFieldReduction MackeyScalarRestriction
  PrimeLocalRing FusionSystems FusionOrbit FusionMackeyShape
  BarComplex BarHigherLimitVanishing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPFusionOrbit DPMackeyPrimeLocalField
  DPMackeyScalarRestriction DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Module DPMackeyPrimeLocalAlgebra.
Section AlgebraReduction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation Zp := [the comPzRingType of (DPPrimeLocal.type p : Type)].
Local Notation K := [the comPzRingType of 'F_p].
Variable R : comPzRingType.
Variable phi : {rmorphism Zp -> R}.

Hypothesis field_acyclic : forall N : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
  mackey_bar_acyclic (centric_inclusion F) N.

Theorem prime_local_algebra_centric_bar_of_prime_field
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic (centric_inclusion F) M.
Proof.
apply/(restricted_mackey_bar_acyclic_iff phi M (centric_inclusion F)).
exact (@prime_local_centric_bar_of_prime_field S F p hp field_acyclic
  (restricted_mackey phi M)).
Qed.

Theorem prime_local_algebra_centric_higher_of_prime_field
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) :
    forall n (q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n.+1), q = 0.
Proof.
apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M)).
exact: prime_local_algebra_centric_bar_of_prime_field.
Qed.

Theorem prime_local_algebra_inclusion_higher_of_prime_field
    (M : mackey_pair R (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit R
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
have he : mackey_codiagram (centric_inclusion F)
    (DPMackeyFusion.full_mackey_of_inclusions hM) =
    pair_codiagram (pair_restrict M (centric_inclusion F)).
  rewrite /mackey_codiagram /pair_codiagram /pair_restrict.
  f_equal; apply Prop_irrelevance.
rewrite -he.
exact (@prime_local_algebra_centric_higher_of_prime_field
  (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

End AlgebraReduction.
End DPMackeyPrimeLocalAlgebra.
