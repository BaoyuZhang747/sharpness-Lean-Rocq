(** The fusion system induced by a finite group on a Sylow subgroup is
    saturated. Both ordinary saturation clauses are proved by actual
    normalizer actions and extensions; no saturation input is assumed. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionSystems FusionSaturation FusionReceptivityCriterion.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionSubgroups
  FiniteGroupFusionAutomorphisms FiniteGroupFusionExtension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionSaturation.
Section Saturation.
Variable G : finGroupType.
Variable T : {group G}.
Variable p : nat.
Hypothesis sylT : p.-Sylow([set: G]) T.

Theorem saturated : DPFusionSaturation.saturated (DPFiniteGroupFusion.system T) p.
Proof.
apply (@DPFusionReceptivityCriterion.saturated_of_normalized_receptive_sylow
  [the finGroupType of [subg T]%type] (DPFiniteGroupFusion.system T) p
  (DPFiniteGroupFusionSubgroups.sylow_carrier_pgroup sylT)).
move=> P hP; split.
- exact (DPFiniteGroupFusionExtension.fully_normalized_receptive sylT hP).
- exact (DPFiniteGroupFusionAutomorphisms.fully_normalized_automizer_sylow sylT hP).
Qed.

End Saturation.
End DPFiniteGroupFusionSaturation.

Print Assumptions DPFiniteGroupFusionSaturation.saturated.
Check DPFiniteGroupFusionSaturation.saturated.
