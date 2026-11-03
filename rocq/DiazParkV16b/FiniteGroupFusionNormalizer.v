(** Fully normalized subgroups have Sylow normalizers in the ambient group.
    This is an actual finite-group argument, with no saturation assumption. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionCentralizerMaps.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionSubgroups.
Import DPFusion DPFusionSubgroup DPFiniteGroupFusion DPFiniteGroupFusionSubgroups.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionNormalizer.
Section Ambient.
Variable G : finGroupType.
Variable p : nat.
Variable T : {group G}.
Hypothesis sylT : p.-Sylow([set: G]) T.

Theorem sylow_normalizer_of_max (P : {group G}) :
  P \subset T ->
  (forall g : G, P :^ g \subset T ->
    (#|'N_T(P :^ g)| <= #|'N_T(P)|)%N) ->
  p.-Sylow('N(P)) 'N_T(P).
Proof.
move=> sPT hmax.
have pNT : p.-group 'N_T(P) := pgroupS (subsetIl T 'N(P)) (pHall_pgroup sylT).
have [R sylR sNR] := Sylow_superset (subsetIr T 'N(P)) pNT.
have sPR : P \subset R.
  apply: subset_trans sNR; by rewrite subsetI sPT normG.
have [g _ sRgT] := Sylow_Jsub sylT (subsetT R) (pHall_pgroup sylR).
have sPgT : P :^ g \subset T.
  apply: subset_trans sRgT; by rewrite conjSg.
have sRgN : R :^ g \subset 'N(P :^ g).
  by rewrite normJ conjSg; exact: pHall_sub sylR.
have sRgNT : R :^ g \subset 'N_T(P :^ g) by rewrite subsetI sRgT sRgN.
have hR : (#|R| <= #|'N_T(P)|)%N.
  have hcard := subset_leq_card sRgNT.
  rewrite cardJg in hcard; exact: leq_trans hcard (hmax g sPgT).
have eqNR : 'N_T(P) = (R : {set G}).
  apply/eqP; by rewrite eqEcard sNR hR.
by rewrite eqNR.
Qed.

End Ambient.

Section Fusion.
Variable G : finGroupType.
Variable T : {group G}.
Local Notation S := [subg T]%type.

Theorem fully_normalized_normalizer_sylow (p : nat)
    (sylT : p.-Sylow([set: G]) T) (P : {group S}) :
  DPFusionSystem.fully_normalized (DPFiniteGroupFusion.system T) P ->
  p.-Sylow('N(ambient P)) 'N_T(ambient P).
Proof.
move=> hP; apply: (sylow_normalizer_of_max sylT (ambient_sub P)).
move=> g hg.
have hconj := @conjugate_from G T P g hg.
have hcard := implyP (forallP hP (from_ambient T (ambient P :^ g)%G)) hconj.
rewrite -!ambient_card !ambient_normalizer (ambient_from hg) in hcard.
exact: hcard.
Qed.

End Fusion.
End DPFiniteGroupFusionNormalizer.

Print Assumptions DPFiniteGroupFusionNormalizer.sylow_normalizer_of_max.
Print Assumptions DPFiniteGroupFusionNormalizer.fully_normalized_normalizer_sylow.
