(** Manuscript Lemma 4.2, discharging the geometric argument with the
    new Diaz--Park trace-image decomposition and summand-vanishing proof. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  FusionMaps FusionSystems FusionOrbit FusionConjugacy FusionCentricBasics
  FusionSaturation FusionCentralizerMaps FusionSubsystemOrbit FusionSubsystemRestriction
  FusionStableElements FusionStableLimit MackeyStructures MackeyPair MackeyPairDiagrams
  MackeyFusionBridge MackeyFusionMinimal FusionMackeyShape
  FusionCentralizer FusionCentralizerAmbient FusionCentralizerSaturation FusionCentralizerCentric.
From DiazParkV29 Require Import SubsystemDegreeZeroCore SimpleFunctor SimpleManuscript.
Import GRing.Theory DPFusion DPFusionSubgroup DPFusionSubsystemRestriction DPFusionStable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV29FusionStableZero.
Section Vanishing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable C : {group S}.
Local Notation T := [subg C]%type.
Variable H : DPFusionSystem.system [the finGroupType of T].
Hypothesis hH : forall (P Q : {group T}) (f : DPFusion.map P Q),
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (lift f).
Hypothesis hcentric : forall P : {group T},
  DPFusionSystem.centric H P -> DPFusionSystem.centric F (ambient P).
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Hypothesis Qnoncentric : ~~ DPFusionSystem.centric F Q.
Variable p : nat.
Hypothesis charp : p%:R = (0 : R).
Hypothesis pT : p.-group [set: T].
Hypothesis satH : DPFusionSaturation.saturated H p.
Let N := restricted_pair hH M.

Lemma label_minimal : DPMackeyMinimal.subgroup_minimal full Q.
Proof.
split; first exact: leastQ.1.
move=> U hU x; apply: leastQ.2; exact: proper_card hU.
Qed.

Theorem subsystem_centric_limit_zero
    (y : module_limit_type (DPFusionStableLimit.centric_coefficient N)) : y = 0.
Proof.
refine (@DPV29FusionStableZeroCore.subsystem_centric_limit_zero S F C H hH hcentric
  R M Q Qnoncentric p pT _ _ satH y).
- move=> U x hx.
  exact (@DPSimpleFunctor.simple_functor_restriction_detection
    S F R full simple Q label_minimal U x hx).
- move=> L U hQL hLU pU noncentric x.
  exact (@DPSimpleManuscript.simple_functor_centralizer_restriction_zero
    S F R full simple Q label_minimal L U hLU hQL p charp pU noncentric x).
Qed.
End Vanishing.
End DPV29FusionStableZero.

Module DPV29CentralizerLimitZero.
Section Vanishing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).

Definition centralizer_pair := DPFusionSubsystemRestriction.restricted_pair
  (@DPFusionCentralizerAmbient.lift_allowed S F E) M.
Definition centralizer_coefficient := DPFusionStableLimit.centric_coefficient centralizer_pair.

Hypothesis abE : abelian E.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Hypothesis hE : DPFusionSystem.fully_centralized F E.
Hypothesis charp : p%:R = (0 : R).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Hypothesis Qnoncentric : ~~ DPFusionSystem.centric F Q.

Theorem centralizer_limit_zero (y : module_limit_type centralizer_coefficient) : y = 0.
Proof.
exact (@DPV29FusionStableZero.subsystem_centric_limit_zero S F 'C(E)%G
  (DPFusionCentralizer.system F E) (@DPFusionCentralizerAmbient.lift_allowed S F E)
  (@DPFusionCentralizerCentric.centralizer_centric_ambient_centric S F E abE p pS sat hE)
  R M hM simple Q leastQ Qnoncentric p charp
  (@DPFusionCentralizerSaturation.centralizer_pgroup S E p pS)
  (DPFusionCentralizerSaturation.centralizer_saturated abE pS sat hE) y).
Qed.
End Vanishing.
End DPV29CentralizerLimitZero.

Print Assumptions DPV29FusionStableZero.subsystem_centric_limit_zero.
Print Assumptions DPV29CentralizerLimitZero.centralizer_limit_zero.
