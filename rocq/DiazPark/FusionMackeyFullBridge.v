From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionMackeyShape
  FusionMackeyRepresentatives FusionMackeyDoubleCosetTransport FusionMackeyFullBridgeGeometry
  MackeyStructures MackeyPair MackeyFusionBridge.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey DPMackeyRepresentatives
  DPMackeyDoubleCosetTransport DPFusionMackeyFullGeometry DPMackeyFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyFullBridge.
Lemma pair_full_roundtrip (R : comPzRingType) (C : category) (B : mackey_shape C)
    (M : mackey_module R B) (h : pair_mackey_formula (pair_of_mackey M) B) :
  mackey_module_of_pair h = M.
Proof.
case: M h => v r t ri ti rc tc iso formula h /=.
have eh : h = formula := Prop_irrelevance _ _.
by rewrite eh.
Qed.

Section NativeFull.
Variable S : finGroupType.
Variable F : system S.
Variable R : comPzRingType.
Variable M : mackey_module R (fusion_mackey_shape F).

Theorem full_inclusion_mackey : inclusion_mackey_formula (pair_of_mackey M).
Proof.
move=> P Q T hP hQ x.
pose f := repr (orbit_class (inclusion_arrow F hP)).
pose g := repr (orbit_class (inclusion_arrow F hQ)).
have /exists_inP[a aT /forall_inP hfa] :=
  target_inner_reverse (representative_related (inclusion_arrow F hP)).
have /exists_inP[b bT /forall_inP hgb] :=
  target_inner_reverse (representative_related (inclusion_arrow F hQ)).
have hf : {in P, val f =1 (fun y => (y ^ a)%g)}.
  move=> y Py; have h := eqP (hfa y Py).
  change (val f y = (DPFusion.inclusion hP y) ^ a)%g in h.
  by rewrite inclusion_in in h.
have hg : {in Q, val g =1 (fun y => (y ^ b)%g)}.
  move=> y Qy; have h := eqP (hgb y Qy).
  change (val g y = (DPFusion.inclusion hQ y) ^ b)%g in h.
  by rewrite inclusion_in in h.
have eF := conjugation_image hf.
have eG := conjugation_image hg.
have h := @mackey_formula R (orbit_category F) (fusion_mackey_shape F) M P Q T
  (orbit_class (inclusion_arrow F hP)) (orbit_class (inclusion_arrow F hQ)) x.
change (pair_pull (pair_of_mackey M) (orbit_class (inclusion_arrow F hQ))
  (pair_push (pair_of_mackey M) (orbit_class (inclusion_arrow F hP)) x) =
  \sum_(i : double_coset_index (DPFusion.image (val f)) (DPFusion.image (val g)) T)
    pair_push (pair_of_mackey M) (orbit_class (raw_right f g (double_coset_representative i)))
      (pair_pull (pair_of_mackey M) (orbit_class (raw_left f g (double_coset_representative i))) x)) in h.
rewrite h.
rewrite (bigop.reindex (@translated_index S P Q T _ _ a b aT bT eF eG)
  (onW_bij _ (translated_index_bijective aT bT eF eG))) /=.
apply: eq_bigr=> i _.
rewrite (@conjugated_raw_summand S F P Q T f g a b hf hg R (pair_of_mackey M)).
change (@inclusion_summand S F R (pair_of_mackey M) P Q
  (untranslate a b (double_coset_representative (translated_index aT bT eF eG i))) x =
  @inclusion_summand S F R (pair_of_mackey M) P Q (double_coset_representative i) x).
exact: (@same_double_coset_summand S F R (pair_of_mackey M) P Q _ _
  (untranslated_representative aT bT eF eG i) x).
Qed.

Theorem full_inclusion_roundtrip :
  full_mackey_of_inclusions full_inclusion_mackey = M.
Proof.
exact: pair_full_roundtrip.
Qed.
End NativeFull.
End DPFusionMackeyFullBridge.

Print Assumptions DPFusionMackeyFullBridge.full_inclusion_mackey.
Print Assumptions DPFusionMackeyFullBridge.full_inclusion_roundtrip.
