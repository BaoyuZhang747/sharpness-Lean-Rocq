From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge
  MackeyBarReduction MackeyArbitraryCoefficients FusionSystems FusionOrbit
  FusionMackeyShape FusionFiniteCategory BarComplex BarHigherLimitVanishing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Module DPMackeyHigherReduction.
Section CentricReduction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable K : fieldType.

Definition centric_finite_inclusion :=
  functor_comp (DPFusionFinite.finite_to_centric F) (centric_inclusion F).

Theorem simple_to_arbitrary_centric_bar
    (simple_acyclic : forall M : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple M -> mackey_bar_acyclic (centric_inclusion F) M)
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic (centric_inclusion F) M.
Proof.
exact (@DPMackeyArbitrary.simple_to_arbitrary_mackey_acyclic S F K
  (DPFusionFinite.centric_finite_category F) centric_finite_inclusion simple_acyclic M).
Qed.

Definition centric_higher_acyclic (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) :=
  forall n (q : derived_limit K (mackey_codiagram (centric_inclusion F) M) n.+1), q = 0.

Theorem simple_to_arbitrary_centric_higher_limits
    (simple_acyclic : forall M : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple M -> centric_higher_acyclic M)
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) :
    centric_higher_acyclic M.
Proof.
apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M)).
apply: simple_to_arbitrary_centric_bar => N hN.
apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) N)).
exact: simple_acyclic hN.
Qed.

(** This endpoint uses precisely the manuscript's inclusion-only Mackey
    input and its original paired-functor coefficient diagram. *)
Theorem inclusion_simple_to_arbitrary_centric_higher_limits
    (simple_acyclic : forall M : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple M -> centric_higher_acyclic M)
    (M : mackey_pair K (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit K
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
have he : mackey_codiagram (centric_inclusion F)
    (DPMackeyFusion.full_mackey_of_inclusions hM) =
    pair_codiagram (pair_restrict M (centric_inclusion F)).
  rewrite /mackey_codiagram /pair_codiagram /pair_restrict.
  f_equal; apply Prop_irrelevance.
rewrite -he.
exact (@simple_to_arbitrary_centric_higher_limits simple_acyclic
  (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

End CentricReduction.
End DPMackeyHigherReduction.

