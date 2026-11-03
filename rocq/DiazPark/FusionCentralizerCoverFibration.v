From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFibration FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentralizerCover FusionCentralizerCoverProjection FusionCentralizerCoverLifts.
Import DPFusion DPFusionOrbit DPFusionCentralizerCover DPFusionCentralizerCoverProjection
  DPFusionCentralizerCoverLifts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverFibration.
Section Fibration.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.

Lemma elementary_equality_arrowE (E D : elementary_object F p) (e : E = D) :
  {in val E, forall x,
    val (@equality_arrow (opposite (opposite (elementary_category F p))) E D e) x = x}.
Proof. case: D / e; exact: DPFusion.identity_in. Qed.

Definition projection_cartesian_lift (X : centralized_object F p)
    (B : elementary_object F p)
    (theta : DPFusionSystem.arrow F (val B) (elementary (val X))) :
    cartesian_lift (functor_op (projection F p)) X B theta.
Proof.
have eB : projection_object (centralized_target sat theta) = B by apply: val_inj.
refine (@Build_cartesian_lift (opposite (centralized_category F p))
  (opposite (opposite (elementary_category F p))) (functor_op (projection F p)) X B theta
  (centralized_target sat theta) eB (lift_arrow sat theta) _ _).
- apply: DPFusionSystem.arrow_ext=> x Bx.
  change (delta (lift_arrow sat theta) x =
    DPFusion.compose (val (@equality_arrow (opposite (opposite (elementary_category F p))) _ _ eB)) (val theta) x).
  rewrite lift_delta DPFusion.compose_in // elementary_equality_arrowE //.
- exact: lift_cocartesian.
Defined.

Definition projection_op_fibration : fibration (functor_op (projection F p)) :=
  fun X B theta => @projection_cartesian_lift X B theta.
End Fibration.
End DPFusionCentralizerCoverFibration.


