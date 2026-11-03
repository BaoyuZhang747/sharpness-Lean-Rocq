(** The actual degree-zero centralizer coefficient in the sharpness proof. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  FusionMaps FusionSystems FusionOrbit FusionSaturation FusionCentralizer
  FusionCentralizerAmbient FusionCentralizerSaturation FusionCentralizerCentric
  FusionSubsystemRestriction FusionStableLimit FusionStableZero
  MackeyPair MackeyStructures MackeyFusionBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPCentralizerLimitZero.
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
  exact (@DPFusionStableZero.subsystem_centric_limit_zero S F 'C(E)%G
    (DPFusionCentralizer.system F E) (@DPFusionCentralizerAmbient.lift_allowed S F E)
    (@DPFusionCentralizerCentric.centralizer_centric_ambient_centric S F E abE p pS sat hE)
    R M hM simple Q leastQ Qnoncentric p charp
    (@DPFusionCentralizerSaturation.centralizer_pgroup S E p pS)
    (DPFusionCentralizerSaturation.centralizer_saturated abE pS sat hE) y).
Qed.

End Vanishing.
End DPCentralizerLimitZero.
