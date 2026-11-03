(** The centralizer detector specializes to the actual subsystem-restricted
    Mackey pair used by the induction. The coefficient identification is a
    literal equality of functors, not an extra hypothesis. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryModules CategoryDerivedLimits
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizer
  FusionCentralizerCoverProjection FusionCentralizerCoverFiberCoefficients
  FusionCentralizerDetection FusionCentralizerLimitZero FusionStableLimit
  MackeyPair MackeyPairDiagrams.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionCentralizerDetectionMackey.
Section Detection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).

Lemma centralizer_restriction_pair_eq (B : DPFusionCentralizerCoverProjection.elementary_object F p) :
    @DPFusionCentralizerDetection.centralizer_restriction S F p pS sat R
      (DPFusionStableLimit.centric_coefficient M) B =
    @DPCentralizerLimitZero.centralizer_coefficient S F (val B) R M.
Proof.
apply (@functor_extensionality
  (opposite (DPFusionOrbit.centric_orbit_category (DPFusionCentralizer.system F (val B))))
  (module_category R)
  (@DPFusionCentralizerDetection.centralizer_restriction S F p pS sat R
    (DPFusionStableLimit.centric_coefficient M) B)
  (@DPCentralizerLimitZero.centralizer_coefficient S F (val B) R M)
  (Logic.eq_refl _)). reflexivity.
Qed.

Theorem mackey_centralizer_detection (ntS : [set: S] :!=: 1%G)
    (centralizers_zero : forall (B : DPFusionCentralizerCoverProjection.elementary_object F p) n
      (v : derived_limit R (@DPCentralizerLimitZero.centralizer_coefficient S F (val B) R M) n), v = 0) :
    forall n (v : derived_limit R (DPFusionStableLimit.centric_coefficient M) n), v = 0.
Proof.
apply (@DPFusionCentralizerDetection.centralizer_detection S F p pS ntS sat R
  (DPFusionStableLimit.centric_coefficient M)).
intros B n. rewrite centralizer_restriction_pair_eq. exact (@centralizers_zero B n).
Qed.
End Detection.
End DPFusionCentralizerDetectionMackey.
