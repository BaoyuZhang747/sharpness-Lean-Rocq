From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionConjugacy FusionSylowAdjustment FusionReceptivity FusionReceptivityTransfer.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionReceptivityCriterion.

Section Criterion.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].

Definition normalized_receptive_sylow :=
  forall P : {group S}, DPFusionSystem.fully_normalized F P ->
    DPFusionReceptivity.receptive F P /\
    p.-Sylow(DPFusionSaturation.aut_group F P)
      (DPFusionSaturation.ambient_aut_group P).

Theorem fully_centralized_receptive :
  normalized_receptive_sylow ->
  forall P : {group S}, DPFusionSystem.fully_centralized F P ->
    DPFusionReceptivity.receptive F P.
Proof.
move=> hcrit P hP.
have [Q [hPQ hQ]] := DPFusionConjugacy.fully_normalized_conjugate_exists F P.
have [recQ sylQ] := hcrit Q hQ.
have /existsP[f /andP[hf /eqP ontof]] := hPQ.
have [theta [htheta [onto hdomain]]] :=
  @DPFusionSylowAdjustment.sylow_adjust_normalizer S F p P Q f pS hf ontof sylQ.
have hext := recQ P theta htheta onto.
rewrite hdomain in hext.
have [eta [heta eta_extends]] := hext.
have hC : 'C(Q) \subset DPFusion.image eta :=
  @DPFusionReceptivityTransfer.centralizer_in_normalizer_image
    S F P Q theta htheta onto eta eta_extends hP.
exact (@DPFusionReceptivityTransfer.transfer_receptive
  S F P Q theta htheta onto eta eta_extends heta hC recQ).
Qed.

Theorem saturated_of_normalized_receptive_sylow :
  normalized_receptive_sylow -> DPFusionSaturation.saturated F p.
Proof.
move=> hcrit; constructor.
- move=> P hP; have [hrec hsyl] := hcrit P hP; split=> //.
  exact: DPFusionReceptivity.receptive_fully_centralized hrec.
- move=> P Q f hf onto hQ.
  exact: (@fully_centralized_receptive hcrit Q hQ P f hf onto).
Qed.

Theorem saturation_iff_normalized_receptive_sylow :
  DPFusionSaturation.saturated F p <-> normalized_receptive_sylow.
Proof.
split; last exact: saturated_of_normalized_receptive_sylow.
move=> hs P hP.
exact (@DPFusionReceptivity.saturated_fully_normalized_receptive S F p hs P hP).
Qed.

End Criterion.
End DPFusionReceptivityCriterion.

