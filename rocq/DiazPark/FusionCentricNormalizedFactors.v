From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans FusionMaps FusionSystems
  FusionOrbit FusionFiniteCategory FusionCentricBasics FusionCentricRestriction
  FusionCentricSpanNormalization FusionCentricNormalizedSpans.
Import DPFusionOrbit DPFusionCentricNormalizedSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricNormalizedFactors.
Section Factors.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Variables P Q : fc_object C.
Variables X A : finite_span C P Q.
Variable h : span_factor X A.
Variable x : DPFusionSystem.arrow F (val (span_object X)) (val P).
Variable a : DPFusionSystem.arrow F (val (span_object A)) (val P).
Hypotheses (hx : orbit_class x = span_first X) (ha : orbit_class a = span_first A).
Hypothesis raw_triangle : DPFusionSystem.arrow_compose (repr (val h)) a = x.

Lemma image_sub_image : DPFusion.image (val x) \subset DPFusion.image (val a).
Proof.
rewrite -raw_triangle.
exact: DPFusionCentricSpanNormalization.composite_image_sub.
Qed.

Local Notation NX := (@normalized_span S F P Q X x).
Local Notation NA := (@normalized_span S F P Q A a).
Local Notation fx := (normalizing_factor hx).
Local Notation fa := (normalizing_factor ha).

Definition normalized_inclusion : fc_hom C (span_object NX) (span_object NA) :=
  DPFusionCentricRestriction.orbit_inclusion F image_sub_image.

Lemma normalized_triangle :
  fc_compose (val fx) normalized_inclusion =
  fc_compose (val h) (val fa).
Proof.
change (orbit_compose (orbit_class (DPFusionCentricSpanNormalization.image_arrow x))
  (DPFusionCentricRestriction.orbit_inclusion F image_sub_image) =
  orbit_compose (val h) (orbit_class (DPFusionCentricSpanNormalization.image_arrow a))).
rewrite -(reprK (val h)) /DPFusionCentricRestriction.orbit_inclusion !orbit_compose_class.
apply: congr1; apply: DPFusionSystem.arrow_ext=> u Uu.
rewrite /DPFusionSystem.arrow_compose /DPFusionCentricSpanNormalization.image_arrow /=.
rewrite !DPFusion.compose_in ?DPFusion.map_into // DPFusion.inclusion_in ?DPFusion.map_into //.
rewrite DPFusion.to_image_in // DPFusion.to_image_in ?DPFusion.map_into //.
have H := congr1 (fun f : DPFusionSystem.arrow F (val (span_object X)) (val P) =>
  DPFusion.map_fun (val f) u) raw_triangle.
by rewrite /DPFusionSystem.arrow_compose /= DPFusion.compose_in // in H; symmetry.
Qed.

Lemma normalizing_cancel (T : fc_object C) (f g : fc_hom C (span_object NX) T) :
  fc_compose (val fx) f = fc_compose (val fx) g -> f = g.
Proof.
move=> heq.
have H := congr1 (fun t => fc_compose (iso_inv (@normalizing_iso S F P Q X x)) t) heq.
rewrite -!fc_assoc in H.
have Hi := iso_inv_hom (@normalizing_iso S F P Q X x).
change (fc_compose (iso_inv (@normalizing_iso S F P Q X x)) (val fx) = fc_identity (span_object NX)) in Hi.
by rewrite Hi !fc_id_left in H.
Qed.

Definition normalized_factor : span_factor NX NA.
Proof.
exists normalized_inclusion.
apply/andP; split; apply/eqP; apply: normalizing_cancel.
- by rewrite -fc_assoc normalized_triangle fc_assoc !span_factor_first.
- by rewrite -fc_assoc normalized_triangle fc_assoc !span_factor_second.
Defined.

Lemma normalized_factor_triangle :
  span_factor_compose fx normalized_factor = span_factor_compose h fa.
Proof. apply: val_inj; exact: normalized_triangle. Qed.

End Factors.
End DPFusionCentricNormalizedFactors.
