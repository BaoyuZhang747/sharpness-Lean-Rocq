(** Diaz--Park Proposition 4.3-style reduction for the composition factors
    of one specified finite-dimensional Mackey functor.  The assumption
    ranges only over the noncentric-minimal factors in its actual series. *)
From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionSaturation FusionOrbit FusionMackeyShape FusionConjugacy
  FusionCentricBasics FusionCentricAcyclicity MackeyStructures MackeySubquotients
  MackeyFiniteLength MackeyPair MackeyPairDiagrams MackeyFusionBridge
  MackeyBarReduction MackeyFusionMinimal BarHigherLimitVanishing.
From DiazParkV16b Require Import MackeyFixedDegreeClosure MackeyMinimalSupportManuscript
  MackeyNoncentricSimpleReduction.
From DiazParkV29 Require Import CompositionSeries CompositionExact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPCompositionSeries DPCompositionExact
  DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPCompositionReduction.
Section CompositionFactors.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable K : fieldType.

Definition factor_of_series M (s : composition_series M)
    (T : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) : Prop :=
  List.In T (series_factors s).

Lemma factor_of_series_simple M (s : composition_series M) T :
    factor_of_series s T -> mackey_simple T.
Proof.
move=> hT; apply: (proj1 (List.Forall_forall _ _) (series_factors_simple s) T hT).
Qed.

Definition noncentric_minimal_exists
    (T : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) : Prop :=
  exists Q : {group S}, DPMackeyMinimal.subgroup_minimal T Q /\
    ~~ DPFusionSystem.centric F Q.

Definition positive_centric_limits_zero
    (T : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) : Prop :=
  forall n (q : derived_limit K (mackey_codiagram (centric_inclusion F) T) n.+1), q = 0.

Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Hypothesis charp : p \in [pchar K].

Theorem series_noncentric_factor_reduction M (s : composition_series M)
    (h : forall T, factor_of_series s T -> noncentric_minimal_exists T ->
      positive_centric_limits_zero T) : positive_centric_limits_zero M.
Proof.
elim: s h => [M0 hz|M0 N hs t ih] h.
- apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram (centric_inclusion F) M0)).
  exact: mackey_bar_zero hz.
- have hN : positive_centric_limits_zero (subfunctor_mackey N).
    have [Q leastQ] := DPMackeyMinimal.least_nonzero_exists hs.1.
    case: (boolP (DPFusionSystem.centric F Q)) => [centricQ|noncentricQ].
    + exact (@DPFusionCentricAcyclicity.field_simple_centric_higher_limits_zero
        S F p K charp pS sat (subfunctor_mackey N) hs Q leastQ centricQ).
    + apply: h; first by left.
      exists Q; split=> //.
      split; first exact: leastQ.1.
      move=> U hU x; apply: leastQ.2; exact: proper_card hU.
  have hQ : positive_centric_limits_zero (quotient_mackey N).
    apply: ih => T hT hnon; apply: h hnon.
    by right.
  move=> n; exact (@subquotient_derived_extension_zero K (orbit_category F)
    (centric_orbit_category F) (DPFusionMackey.fusion_mackey_shape F)
    (centric_inclusion F) M0 N n.+1 (hN n) (hQ n)).
Qed.

Theorem finite_noncentric_composition_factor_reduction
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F))
    (hM : mackey_finite_values M) :
    exists s : composition_series M,
      (forall T, factor_of_series s T -> noncentric_minimal_exists T ->
        positive_centric_limits_zero T) -> positive_centric_limits_zero M.
Proof.
have [s _] := @finite_composition_series_exists K (orbit_category F)
  (DPFusionMackey.fusion_mackey_shape F) [the finType of {group S}]
  (fun P => P) (fun P => ex_intro _ P erefl) M hM.
exists s; exact: series_noncentric_factor_reduction.
Qed.

Lemma one_noncentric_minimal_implies_all T (simpleT : mackey_simple T) :
    noncentric_minimal_exists T ->
    DPMackeyNoncentricReduction.minimal_subgroups_noncentric T.
Proof.
move=> [Q [minimalQ noncentricQ]] P minimalP.
have leastQ := DPMackeyMinimalManuscript.minimal_is_least simpleT minimalQ.
have hc := @DPMackeyMinimal.minimal_conjugate S F K T Q leastQ simpleT P minimalP.
apply/negP => centricP; apply: (negP noncentricQ).
exact: DPFusionCentricBasics.centric_conjugate
  (DPFusionConjugacy.conjugate_reverse hc) centricP.
Qed.

Theorem finite_from_noncentric_simple_hypothesis
    (h : forall T : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple T -> DPMackeyNoncentricReduction.minimal_subgroups_noncentric T ->
      positive_centric_limits_zero T)
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F))
    (hM : mackey_finite_values M) : positive_centric_limits_zero M.
Proof.
have [s hs] := finite_noncentric_composition_factor_reduction hM.
apply: hs => T hT hn.
have simpleT := factor_of_series_simple hT.
exact: h simpleT (one_noncentric_minimal_implies_all simpleT hn).
Qed.

End CompositionFactors.
End DPCompositionReduction.

Print Assumptions DPCompositionReduction.series_noncentric_factor_reduction.
Print Assumptions DPCompositionReduction.finite_noncentric_composition_factor_reduction.
Print Assumptions DPCompositionReduction.finite_from_noncentric_simple_hypothesis.
