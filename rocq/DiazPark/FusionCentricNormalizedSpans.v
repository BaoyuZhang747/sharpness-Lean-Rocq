From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans FusionMaps FusionSystems
  FusionOrbit FusionFiniteCategory FusionCentricBasics FusionCentricRestriction FusionCentricSpanNormalization.
Import DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricNormalizedSpans.
Section NormalizedSpan.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Variables P Q : fc_object C.
Variable A : finite_span C P Q.
Variable a : DPFusionSystem.arrow F (val (span_object A)) (val P).
Hypothesis ha : orbit_class a = span_first A.

Definition normalized_object : fc_object C :=
  Sub (DPFusion.image (val a)) (DPFusionCentricBasics.centric_image (valP a) (valP (span_object A))).
Definition normalizing_iso : @isomorphism (fc_category C) (span_object A) normalized_object.
Proof.
pose e := DPFusionCentricSpanNormalization.orbit_image_iso a.
refine (@Build_isomorphism (fc_category C) (span_object A) normalized_object
  (iso_hom e) (iso_inv e) _ _).
- exact (iso_hom_inv e).
- exact (iso_inv_hom e).
Defined.

Definition normalized_span : finite_span C P Q :=
  existT (fun U => (fc_hom C U P * fc_hom C U Q)%type) normalized_object
    (DPFusionCentricRestriction.orbit_inclusion F (DPFusion.image_sub (val a)),
      fc_compose (iso_inv normalizing_iso) (span_second A)).

Definition normalizing_factor : span_factor A normalized_span.
Proof.
exists (iso_hom normalizing_iso); apply/andP; split; apply/eqP.
- change (orbit_compose (iso_hom (DPFusionCentricSpanNormalization.orbit_image_iso a))
    (DPFusionCentricRestriction.orbit_inclusion F (DPFusion.image_sub (val a))) = span_first A).
  by rewrite DPFusionCentricSpanNormalization.orbit_image_factorization ha.
- change (fc_compose (iso_hom normalizing_iso)
    (fc_compose (iso_inv normalizing_iso) (span_second A)) = span_second A).
  rewrite -fc_assoc.
  have h := iso_hom_inv normalizing_iso.
  change (fc_compose (iso_hom normalizing_iso) (iso_inv normalizing_iso) = fc_identity (span_object A)) in h.
  by rewrite h fc_id_left.
Defined.

Definition normalized_span_iso :
  @isomorphism (fc_category (finite_span_category C P Q)) A normalized_span :=
  @span_factor_iso C P Q A normalized_span normalizing_factor normalizing_iso erefl.

Lemma normalized_first : span_first normalized_span =
  DPFusionCentricRestriction.orbit_inclusion F (DPFusion.image_sub (val a)).
Proof. reflexivity. Qed.

End NormalizedSpan.
End DPFusionCentricNormalizedSpans.
