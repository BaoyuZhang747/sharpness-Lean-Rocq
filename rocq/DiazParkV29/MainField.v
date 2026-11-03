(** Order induction using the v2.9 composition-series/direct-limit reduction
    and the new trace-decomposition branches.  All coefficient values are
    arbitrary; the quotient-system construction and Route B are retained. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup abelian boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionOrbit FusionSaturation FusionMackeyShape
  FusionCentralizer FusionCentralizerCentral FusionCentralizerSaturation
  FusionCentralizerCoverProjection FusionQuotientConstruction
  FusionCentricAcyclicity FusionSharpnessStatement FusionSharpnessInductionGeometry
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyBarReduction MackeyFusionBridge
  MackeyFusionMinimal MackeyDiagramIdentities FusionMackeyFullBridge.
From DiazParkV29 Require Import CompositionReduction ReductionManuscript
  MainCentralizer MainCentralQuotient.
Import GRing.Theory DPFusionOrbit DPCompositionReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV29DiazPark.
Theorem centralizer_criterion (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (K : fieldType) (charp : p \in [pchar K])
    (centralizers_sharp : forall B : DPFusionCentralizerCoverProjection.elementary_object F p,
      DPFusionSharpness.sharpness K (DPFusionCentralizer.system F (val B))) :
    DPFusionSharpness.sharpness K F.
Proof.
move=> M.
apply (@DPV29MackeyReduction.noncentric_simple_to_arbitrary_higher_limits
  S F p pS sat K charp) => N simpleN noncentricN.
have [Q leastQ] := DPMackeyMinimal.least_nonzero_exists simpleN.1.
have minimalQ : DPMackeyMinimal.subgroup_minimal N Q.
  split; first exact: leastQ.1.
  move=> U hU x; apply: leastQ.2; exact: proper_card hU.
have noncentricQ := noncentricN Q minimalQ.
have simpleP : mackey_simple (DPMackeyFusion.full_mackey_of_inclusions
    (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)).
  by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
have leastP : mackey_least_nonzero (DPMackeyFusion.full_mackey_of_inclusions
    (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)) (fun A : {group S} => #|A|) Q.
  by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
rewrite /positive_centric_limits_zero native_pair_codiagram pair_restrict_codiagram.
move=> n.
exact (@DPV29SharpnessCentralizer.noncentric_simple_all_zero S F p pS sat K charp
  centralizers_sharp (pair_of_mackey N) (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)
  simpleP Q leastP noncentricQ n.+1).
Qed.

Theorem field_sharpness (p : nat) (K : fieldType) (charp : p \in [pchar K]) :
    forall (S : finGroupType) (F : DPFusionSystem.system S),
      p.-group [set: S] -> DPFusionSaturation.saturated F p -> DPFusionSharpness.sharpness K F.
Proof.
apply (@DPFusionSharpnessInductionGeometry.saturated_fusion_order_induction p
  (fun S F => DPFusionSharpness.sharpness K F)).
move=> S F pS sat IH.
apply (@centralizer_criterion S F p pS sat K charp).
move=> B. have /and3P[ntE elE fcE] := valP B.
have abE : abelian (val B) := abelem_abelian elE.
apply (@DPV29CentralQuotientSharpness.central_quotient_sharpness
  [the finGroupType of ([subg 'C(val B)%G]%type)] (DPFusionCentralizer.system F (val B))
  (DPFusionCentralizerCentral.embedded (val B))
  (DPFusionCentralizerCentral.embedded_central F abE) p
  (DPFusionCentralizerSaturation.centralizer_pgroup (val B) pS)
  (DPFusionCentralizerSaturation.centralizer_saturated abE pS sat fcE) K charp).
exact (@IH (DPFusionSharpnessInductionGeometry.quotient_type (val B))
  (DPFusionSharpnessInductionGeometry.quotient_system F abE)
  (DPFusionSharpnessInductionGeometry.quotient_carrier_lt abE ntE)
  (DPFusionSharpnessInductionGeometry.quotient_pgroup (val B) pS)
  (DPFusionSharpnessInductionGeometry.quotient_saturated abE pS sat fcE)).
Qed.

Theorem diaz_park_theorem (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (K : fieldType) (charp : p \in [pchar K])
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) n :
    forall q : derived_limit K (mackey_codiagram (centric_inclusion F) M) n.+1, q = 0.
Proof. exact (@field_sharpness p K charp S F pS sat M n). Qed.
End DPV29DiazPark.

Print Assumptions DPV29DiazPark.centralizer_criterion.
Print Assumptions DPV29DiazPark.field_sharpness.
