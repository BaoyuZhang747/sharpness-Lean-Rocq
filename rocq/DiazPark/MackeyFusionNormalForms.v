From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category MackeyStructures MackeyNormalForms
  FusionMaps FusionSystems FusionConjugacy FusionOrbit FusionMackeyShape FusionOrbitRanks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPMackeyNormal.
Section FusionNormalForms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).

(** The exact geometric kind displayed in the manuscript: two actual
    subgroups and an onto allowed fusion homomorphism between them. *)
Record fusion_normal_form (P Q : {group S}) := FusionNormalForm {
  normal_source : {group S};
  normal_target : {group S};
  normal_source_sub : normal_source \subset P;
  normal_target_sub : normal_target \subset Q;
  normal_iso : DPFusionSystem.arrow F normal_source normal_target;
  normal_iso_onto : DPFusion.image (val normal_iso) = normal_target
}.

Definition normal_action P Q (s : fusion_normal_form P Q) (x : mackey_value M P) :=
  mackey_push M (orbit_class (DPFusionMackey.inclusion_arrow F (normal_target_sub s)))
    (mackey_push M (orbit_class (normal_iso s))
      (mackey_pull M (orbit_class (DPFusionMackey.inclusion_arrow F (normal_source_sub s))) x)).

Definition raw_normal_form A P Q (a : DPFusionSystem.arrow F A P)
    (b : DPFusionSystem.arrow F A Q) : fusion_normal_form P Q.
Proof.
refine (@FusionNormalForm P Q (DPFusion.image (val a)) (DPFusion.image (val b))
  (DPFusion.image_sub (val a)) (DPFusion.image_sub (val b))
  (DPFusionSystem.arrow_compose (DPFusionMackey.inverse_arrow a)
    (DPFusionMackey.image_arrow b)) _).
apply: DPFusionRanks.raw_equal_rank_image.
by rewrite !DPFusionConjugacy.map_image_card.
Defined.

Lemma raw_normal_form_action A P Q (a : DPFusionSystem.arrow F A P)
    (b : DPFusionSystem.arrow F A Q) x :
    mackey_push M (orbit_class b) (mackey_pull M (orbit_class a) x) =
      normal_action (raw_normal_form a b) x.
Proof.
rewrite -(DPFusionMackey.orbit_image_factorization a)
  -(DPFusionMackey.orbit_image_factorization b)
  mackey_pull_comp mackey_push_comp mackey_pull_iso.
rewrite /normal_action /raw_normal_form /=.
rewrite -DPFusionOrbit.orbit_compose_class.
change (mackey_push M (orbit_class (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val b))))
  (mackey_push M (orbit_class (DPFusionMackey.image_arrow b))
    (mackey_push M (orbit_class (DPFusionMackey.inverse_arrow a))
      (mackey_pull M (orbit_class (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val a)))) x))) =
  mackey_push M (orbit_class (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val b))))
    (mackey_push M (@Category.compose (orbit_category F) _ _ _ (orbit_class (DPFusionMackey.inverse_arrow a))
      (orbit_class (DPFusionMackey.image_arrow b)))
      (mackey_pull M (orbit_class (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val a)))) x))).
by rewrite mackey_push_comp.
Qed.

Definition span_normal_form P Q (s : @mackey_span (orbit_category F) P Q) :
    fusion_normal_form P Q := raw_normal_form (repr (span_left s)) (repr (span_right s)).

Lemma span_to_inclusion_iso_transfer P Q (s : @mackey_span (orbit_category F) P Q) x :
    span_action (M := M) s x = normal_action (span_normal_form s) x.
Proof.
rewrite /span_action /span_normal_form -raw_normal_form_action.
by rewrite /orbit_class !reprK.
Qed.

Theorem every_structure_composite_has_fusion_normal_form P Q f :
    @structure_composite R (orbit_category F) (DPFusionMackey.fusion_mackey_shape F) M P Q f ->
    exists ss : seq (fusion_normal_form P Q),
      forall x : mackey_value M P, f x = \sum_(s <- ss) normal_action s x.
Proof.
move=> hf; have [ss hs] := every_structure_composite_normalizes hf.
exists [seq span_normal_form s | s <- ss] => x.
rewrite hs big_map; apply: eq_bigr => s _.
exact: span_to_inclusion_iso_transfer.
Qed.

End FusionNormalForms.
End DPMackeyNormal.


