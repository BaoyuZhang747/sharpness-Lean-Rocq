From mathcomp Require Import all_boot all_algebra all_fingroup boolp rat.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge
  MackeyBarReduction MackeyPrimeLocalReduction PrimeLocalRing
  FusionSystems FusionOrbit FusionMackeyShape FusionFiniteCategory
  BarComplex BarHigherLimitVanishing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPFusionOrbit DPMackeyPrimeLocal
  DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Module DPMackeyPrimeLocalHigher.
Section CentricReduction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation R := (DPPrimeLocal.type p).

Definition local_centric_finite_inclusion :=
  functor_comp (DPFusionFinite.finite_to_centric F) (centric_inclusion F).

Hypothesis torsion_acyclic : forall M : mackey_module R (DPFusionMackey.fusion_mackey_shape F),
  (forall P (x : mackey_value M P), p%:R *: x = 0) ->
  mackey_bar_acyclic (centric_inclusion F) M.

Theorem prime_local_centric_bar_of_torsion
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic (centric_inclusion F) M.
Proof.
exact (@arbitrary_prime_local_acyclic S F p hp
  (DPFusionFinite.centric_finite_category F) local_centric_finite_inclusion torsion_acyclic M).
Qed.

Theorem prime_local_centric_higher_of_torsion
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) :
    forall n (q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n.+1), q = 0.
Proof.
apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M)).
exact: prime_local_centric_bar_of_torsion.
Qed.

Theorem prime_local_inclusion_higher_of_torsion
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
exact (@prime_local_centric_higher_of_torsion (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

End CentricReduction.
End DPMackeyPrimeLocalHigher.
