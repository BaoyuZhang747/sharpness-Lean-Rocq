(** Diaz--Park sharpness over every field of characteristic p, with arbitrary
    module values. All geometric and homological auxiliary inputs are proved. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup abelian boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionOrbit FusionSaturation FusionMackeyShape
  FusionCentralizer FusionCentralizerCentral FusionCentralizerSaturation
  FusionCentralizerCoverProjection FusionQuotientConstruction
  FusionCentricAcyclicity FusionSharpnessStatement FusionSharpnessCentralizer
  FusionCentralQuotientSharpness FusionSharpnessInductionGeometry
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyBarReduction MackeyFusionBridge
  MackeyFusionMinimal MackeyHigherLimitReduction MackeyDiagramIdentities FusionMackeyFullBridge.
Import GRing.Theory DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPDiazPark.
Theorem centralizer_criterion (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (K : fieldType) (charp : p \in [pchar K])
    (centralizers_sharp : forall B : DPFusionCentralizerCoverProjection.elementary_object F p,
      DPFusionSharpness.sharpness K (DPFusionCentralizer.system F (val B))) :
    DPFusionSharpness.sharpness K F.
Proof.
  move=> M. apply (@DPMackeyHigherReduction.simple_to_arbitrary_centric_higher_limits S F K) => N simpleN.
  have [Q leastQ] := DPMackeyMinimal.least_nonzero_exists simpleN.1.
  case: (boolP (DPFusionSystem.centric F Q)) => [centricQ|noncentricQ].
  - exact (@DPFusionCentricAcyclicity.field_simple_centric_higher_limits_zero
      S F p K charp pS sat N simpleN Q leastQ centricQ).
  - have simpleP : mackey_simple (DPMackeyFusion.full_mackey_of_inclusions
        (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)).
      by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
    have leastP : mackey_least_nonzero (DPMackeyFusion.full_mackey_of_inclusions
        (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)) (fun A : {group S} => #|A|) Q.
      by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
    rewrite /DPMackeyHigherReduction.centric_higher_acyclic native_pair_codiagram pair_restrict_codiagram.
    move=> n.
    exact (@DPFusionSharpnessCentralizer.noncentric_simple_all_zero S F p pS sat K charp
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
  apply (@DPFusionCentralQuotientSharpness.central_quotient_sharpness
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
End DPDiazPark.
