(** The local fibre's equality arrow acts as the identity on E. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryComma CategoryStructured CategoryFibration
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizer
  FusionCentralizerCoverProjection FusionCentralizerCoverFiberObjects
  FusionCentralizerCoverFibration.
From DiazParkBLO Require Import BLOE3Pointwise.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPFusionCentralizerCoverProjection.
Local Open Scope group_scope.

Module DPBLOE3LocalArrow.
Lemma local_comma_arrow_in (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (B : elementary_object F p) (P : centric_object (DPFusionCentralizer.system F (val B)))
    (x : S) (hx : x \in val B) :
  val (structured_arrow (@DPBLOE3Pointwise.local_comma_point S F p pS sat B P)) x = x.
Proof.
exact (@DPFusionCentralizerCoverFibration.elementary_equality_arrowE S F p B _
  (Logic.eq_sym (fiber_equality (@DPFusionCentralizerCoverFiberObjects.fiber_of_local S F p pS sat B P))) x hx).
Qed.
End DPBLOE3LocalArrow.
