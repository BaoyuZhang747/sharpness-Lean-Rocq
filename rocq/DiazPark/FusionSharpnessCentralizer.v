(** The noncentric simple branch of the sharpness criterion. The degree-zero
    centralizer calculation and positive-degree sharpness are both discharged. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup abelian boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits CategoryDerivedDegreeZero
  FusionSystems FusionOrbit FusionSaturation FusionCentralizer FusionCentralizerAmbient
  FusionCentralizerCoverProjection FusionCentralizerLimitZero FusionCentralizerDetectionMackey
  FusionSubsystemMackey FusionStableLimit FusionAlperinInductionTools FusionSharpnessStatement
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  MackeyDiagramIdentities FusionMackeyFullBridge.
Import GRing.Theory DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionSharpnessCentralizer.
Section Criterion.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Hypothesis charp : p \in [pchar K].
Hypothesis centralizers_sharp : forall B : DPFusionCentralizerCoverProjection.elementary_object F p,
  DPFusionSharpness.sharpness K (DPFusionCentralizer.system F (val B)).
Variable M : mackey_pair K (orbit_category F).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Hypothesis noncentricQ : ~~ DPFusionSystem.centric F Q.

Lemma noncentric_ambient_nontrivial : [set: S] :!=: 1%G.
Proof.
  apply/negP => /eqP hS.
  have hQ : Q = [set: S]%G.
    apply: val_inj; apply/eqP; rewrite eqEsubset subsetT /= hS. exact: sub1G.
  by move: noncentricQ; rewrite hQ (DPFusionAlperinInductionTools.centric_top F).
Qed.

Lemma simple_centralizers_all_zero (B : DPFusionCentralizerCoverProjection.elementary_object F p) n :
  forall v : derived_limit K (@DPCentralizerLimitZero.centralizer_coefficient S F (val B) K M) n, v = 0.
Proof.
  have /and3P[ntE elE fcE] := valP B.
  have abE : abelian (val B) := abelem_abelian elE.
  case: n => [|n].
  - apply (@derived_degree_zero_zero K _ (@DPCentralizerLimitZero.centralizer_coefficient S F (val B) K M)).
    exact (@DPCentralizerLimitZero.centralizer_limit_zero S F (val B) K M abE p pS sat fcE
      (pcharf0 charp) hM simple Q leastQ noncentricQ).
  - pose N := @DPSubsystemMackey.restricted_full_mackey S F 'C(val B)%G
      (DPFusionCentralizer.system F (val B))
      (@DPFusionCentralizerAmbient.lift_allowed S F (val B)) K M hM.
    have hn := @centralizers_sharp B N n.
    rewrite /N /DPSubsystemMackey.restricted_full_mackey
      /DPMackeyFusion.full_mackey_of_inclusions of_pair_codiagram pair_restrict_codiagram in hn.
    exact hn.
Qed.

Theorem noncentric_simple_all_zero :
  forall n (v : derived_limit K (DPFusionStableLimit.centric_coefficient M) n), v = 0.
Proof.
  exact (@DPFusionCentralizerDetectionMackey.mackey_centralizer_detection S F p pS sat K M
    noncentric_ambient_nontrivial simple_centralizers_all_zero).
Qed.
End Criterion.
End DPFusionSharpnessCentralizer.
