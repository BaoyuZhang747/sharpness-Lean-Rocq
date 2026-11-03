(** Lemma 2.2(ii), in a single fixed degree including zero.  The old
    finite-cocycle construction is used over arbitrary commutative rings;
    no saturation, field, Noetherian, or finite-value hypothesis is added. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryFinite CategoryModules CategoryDerivedLimits
  ModuleInfrastructure MackeyStructures MackeySubquotients MackeyModuleCarriers
  MackeyModuleMaps MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  MackeyArbitraryCoefficients FusionSystems FusionOrbit FusionMackeyShape
  FusionFiniteCategory HomologicalComplex HomologicalCohomology BarComplex
  BarNaturality BarDerivedComparison BarHigherLimitVanishing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPMackeyArbitrary DiazParkHomological
  DiazParkCohomology DiazParkBarComplex DiazParkBarNaturality
  DiazParkBarDerivedComparison DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Module DPMackeyFixedDegree.

Section FiniteCategory.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable D : finite_category.
Variable L : functor (fc_category D) (orbit_category F).
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).
Variable n : nat.

Theorem finite_subfunctor_bar_closure
    (h : forall N : mackey_subfunctor M,
      (forall P, module_finitely_generated (mackey_value (subfunctor_mackey N) P)) ->
      forall q : cohomology (bar_complex (mackey_codiagram L (subfunctor_mackey N))) n,
        q = 0) :
    forall q : cohomology (bar_complex (mackey_codiagram L M)) n, q = 0.
Proof.
apply/cohomology_zero_iff => z hz.
pose N := cocycle_subfunctor (L := L) z.
have hN : forall P, module_finitely_generated (mackey_value (subfunctor_mackey N) P).
  exact: cocycle_subfunctor_finite_values.
have hl := cocycle_lift_closed hz.
have hb : coboundary (bar_complex (mackey_codiagram L (subfunctor_mackey N))) n
    (cocycle_lift (L := L) z).
  exact: (proj1 (cohomology_zero_iff _ _) (h N hN) _ hl).
have hi := cochain_map_coboundary
  (bar_cochain_map (cocycle_inclusion (L := L) z)) hb.
exact hi.
Qed.

Theorem finite_subfunctor_higher_limit_closure
    (h : forall N : mackey_subfunctor M,
      (forall P, module_finitely_generated (mackey_value (subfunctor_mackey N) P)) ->
      forall q : derived_limit R (mackey_codiagram L (subfunctor_mackey N)) n, q = 0) :
    forall q : derived_limit R (mackey_codiagram L M) n, q = 0.
Proof.
apply/(module_iso_zero_iff (bar_derived_limit_iso (mackey_codiagram L M) n)).
apply: finite_subfunctor_bar_closure => N hN.
apply/(module_iso_zero_iff
  (bar_derived_limit_iso (mackey_codiagram L (subfunctor_mackey N)) n)).
exact: h hN.
Qed.
End FiniteCategory.

Section CentricCategory.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.

(** The actual centric orbit category is finite on its existing objects
    and morphisms.  Its finite presentation is identity on these data. *)
Theorem centric_subfunctor_higher_limit_closure
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) n
    (h : forall N : mackey_subfunctor M,
      (forall P, module_finitely_generated (mackey_value (subfunctor_mackey N) P)) ->
      forall q : derived_limit R
        (mackey_codiagram (centric_inclusion F) (subfunctor_mackey N)) n, q = 0) :
    forall q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n, q = 0.
Proof.
exact (@finite_subfunctor_higher_limit_closure S F R
  (DPFusionFinite.centric_finite_category F)
  (functor_comp (DPFusionFinite.finite_to_centric F) (centric_inclusion F)) M n h).
Qed.

Lemma inclusion_centric_codiagram
    (M : mackey_pair R (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    mackey_codiagram (centric_inclusion F) (DPMackeyFusion.full_mackey_of_inclusions hM) =
    pair_codiagram (pair_restrict M (centric_inclusion F)).
Proof.
rewrite /mackey_codiagram /pair_codiagram /pair_restrict.
f_equal; apply Prop_irrelevance.
Qed.

(** This form concludes vanishing for the original paired functor of
    Definition 2.1, with only its inclusion Mackey formula supplied. *)
Theorem inclusion_subfunctor_higher_limit_closure
    (M : mackey_pair R (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) n
    (h : forall N : mackey_subfunctor (DPMackeyFusion.full_mackey_of_inclusions hM),
      (forall P, module_finitely_generated (mackey_value (subfunctor_mackey N) P)) ->
      forall q : derived_limit R
        (mackey_codiagram (centric_inclusion F) (subfunctor_mackey N)) n, q = 0) :
    forall q : derived_limit R (pair_codiagram (pair_restrict M (centric_inclusion F))) n,
      q = 0.
Proof.
rewrite -(inclusion_centric_codiagram hM).
exact: centric_subfunctor_higher_limit_closure h.
Qed.
End CentricCategory.
End DPMackeyFixedDegree.

Check DPMackeyFixedDegree.finite_subfunctor_higher_limit_closure.
Check DPMackeyFixedDegree.centric_subfunctor_higher_limit_closure.
Check DPMackeyFixedDegree.inclusion_subfunctor_higher_limit_closure.
Print Assumptions DPMackeyFixedDegree.finite_subfunctor_higher_limit_closure.
Print Assumptions DPMackeyFixedDegree.inclusion_subfunctor_higher_limit_closure.
