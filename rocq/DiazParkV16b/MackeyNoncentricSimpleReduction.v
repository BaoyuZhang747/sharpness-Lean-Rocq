(** Lemma 2.3 with exactly the noncentric-minimal simple-case hypothesis.
    The centric simple case is proved separately; no classification input
    and no hypothesis covering all simple functors is added. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionSaturation FusionOrbit FusionMackeyShape FusionConjugacy
  FusionCentricBasics FusionCentricAcyclicity MackeyStructures MackeyPair
  MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction MackeyFusionMinimal
  MackeyHigherLimitReduction.
From DiazParkV16b Require Import MackeyFixedDegreeClosure MackeyMinimalSupportManuscript.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPMackeyNoncentricReduction.
Section NoncentricPredicate.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.

Definition minimal_subgroups_noncentric
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) : Prop :=
  forall Q : {group S}, DPMackeyMinimal.subgroup_minimal M Q ->
    ~~ DPFusionSystem.centric F Q.
End NoncentricPredicate.

Section FieldReduction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Hypothesis charp : p \in [pchar K].

Theorem noncentric_simple_to_arbitrary_higher_limits
    (h : forall N : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple N -> minimal_subgroups_noncentric N ->
      forall n (q : derived_limit K (mackey_codiagram (centric_inclusion F) N) n.+1),
        q = 0)
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) :
    forall n (q : derived_limit K (mackey_codiagram (centric_inclusion F) M) n.+1),
      q = 0.
Proof.
apply: DPMackeyHigherReduction.simple_to_arbitrary_centric_higher_limits => N simpleN.
have [Q leastQ] := DPMackeyMinimal.least_nonzero_exists simpleN.1.
case: (boolP (DPFusionSystem.centric F Q)) => [centricQ|noncentricQ].
- exact (@DPFusionCentricAcyclicity.field_simple_centric_higher_limits_zero
    S F p K charp pS sat N simpleN Q leastQ centricQ).
- have hall : minimal_subgroups_noncentric N.
    move=> P minimalP.
    have hc := @DPMackeyMinimal.minimal_conjugate S F K N Q leastQ simpleN P minimalP.
    apply/negP => centricP; apply: (negP noncentricQ).
    exact: DPFusionCentricBasics.centric_conjugate (DPFusionConjugacy.conjugate_reverse hc) centricP.
  exact: h simpleN hall.
Qed.

Theorem inclusion_noncentric_simple_to_arbitrary_higher_limits
    (h : forall N : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple N -> minimal_subgroups_noncentric N ->
      forall n (q : derived_limit K (mackey_codiagram (centric_inclusion F) N) n.+1),
        q = 0)
    (M : mackey_pair K (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit K
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
rewrite -(DPMackeyFixedDegree.inclusion_centric_codiagram hM).
exact (@noncentric_simple_to_arbitrary_higher_limits h
  (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.
End FieldReduction.

(** Literal Fp coefficient field of the manuscript's Lemma 2.3. *)
Theorem prime_field_noncentric_simple_reduction
    (S : finGroupType) (F : DPFusionSystem.system S) (p : nat) (hp : prime p)
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (h : forall N : mackey_module [the comPzRingType of 'F_p]
        (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple N -> minimal_subgroups_noncentric N ->
      forall n (q : derived_limit [the pzRingType of 'F_p]
        (mackey_codiagram (centric_inclusion F) N) n.+1), q = 0)
    (M : mackey_pair [the comPzRingType of 'F_p] (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit [the pzRingType of 'F_p]
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
exact (@inclusion_noncentric_simple_to_arbitrary_higher_limits
  S F p pS sat [the fieldType of 'F_p] (pchar_Fp hp) h M hM).
Qed.
End DPMackeyNoncentricReduction.

Check DPMackeyNoncentricReduction.noncentric_simple_to_arbitrary_higher_limits.
Check DPMackeyNoncentricReduction.prime_field_noncentric_simple_reduction.
Print Assumptions DPMackeyNoncentricReduction.noncentric_simple_to_arbitrary_higher_limits.
Print Assumptions DPMackeyNoncentricReduction.prime_field_noncentric_simple_reduction.
