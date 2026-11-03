From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category MackeyStructures FusionMaps FusionSystems FusionOrbit FusionMackeyShape
  FusionMackeyRepresentatives TraceNormalizerCosets FusionCentricBasics.
Import DPFusion DPFusionOrbit DPFusionMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricPullbackExistence.
Section Pointwise.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T X : {group S}.
Variables (f : DPFusionSystem.arrow F P T) (g : DPFusionSystem.arrow F Q T)
  (a : DPFusionSystem.arrow F X P) (b : DPFusionSystem.arrow F X Q).
Variable t : S.
Hypothesis same : {in X, forall x,
  DPFusion.compose (val b) (val g) x = (DPFusion.compose (val a) (val f) x)^t}.

Lemma common_image_sub : image (DPFusion.compose (val a) (val f)) \subset raw_apex f g t.
Proof.
apply/subsetP=> y /morphimP[x Xx _ hy].
change (y = DPFusion.compose (val a) (val f) x) in hy; rewrite hy.
rewrite /raw_apex inE mem_conjgV -(@same x Xx) !compose_in //.
apply/andP; split; exact: image_mem (map_into _ Xx).
Qed.

Definition raw_pointwise_factor : DPFusionSystem.arrow F X (raw_apex f g t) :=
  Sub (corestrict common_image_sub)
    (DPFusionSystem.corestriction_allowed common_image_sub
      (DPFusionSystem.composition_closed (valP a) (valP f))).

Lemma pointwise_factor_value : {in X, forall x,
    (val raw_pointwise_factor) x = DPFusion.compose (val a) (val f) x}.
Proof. exact: corestrict_in. Qed.

Lemma raw_pointwise_left : DPFusionSystem.arrow_compose raw_pointwise_factor (raw_left f g t) = a.
Proof.
apply: DPFusionSystem.arrow_ext=> x Xx.
change (DPFusion.compose (val raw_pointwise_factor) (val (raw_left f g t)) x = (val a) x).
rewrite compose_in // raw_left_value ?map_into // pointwise_factor_value // compose_in //.
exact: inverse_cancel (map_into (val a) Xx).
Qed.

Lemma raw_pointwise_right : DPFusionSystem.arrow_compose raw_pointwise_factor (raw_right f g t) = b.
Proof.
apply: DPFusionSystem.arrow_ext=> x Xx.
change (DPFusion.compose (val raw_pointwise_factor) (val (raw_right f g t)) x = (val b) x).
rewrite compose_in // raw_right_value ?map_into // pointwise_factor_value // -(@same x Xx) compose_in //.
exact: inverse_cancel (map_into (val b) Xx).
Qed.
End Pointwise.

Section Translation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T X : {group S}.
Variables (f : DPFusionSystem.arrow F P T) (g : DPFusionSystem.arrow F Q T).
Variables a t b : S.
Hypotheses (Ha : a \in image (val f)) (Kb : b \in image (val g)).
Local Notation e := (@DPMackeyRepresentatives.translated_iso S F (image (val f)) (image (val g)) a t b Ha Kb).

Lemma raw_translated_left : @Category.compose (orbit_category F) _ _ _ (iso_hom e) (orbit_class (raw_left f g t)) =
    orbit_class (raw_left f g (a*t*b)).
Proof.
change (@Category.compose (orbit_category F) _ _ _ (iso_hom e) (span_left (raw_span f g t)) = span_left (raw_span f g (a*t*b))).
rewrite -(raw_left_image_factorization f g t) -Category.compose_assoc DPMackeyRepresentatives.translated_iso_first.
exact: raw_left_image_factorization.
Qed.

Lemma raw_translated_right : @Category.compose (orbit_category F) _ _ _ (iso_hom e) (orbit_class (raw_right f g t)) =
    orbit_class (raw_right f g (a*t*b)).
Proof.
change (@Category.compose (orbit_category F) _ _ _ (iso_hom e) (span_right (raw_span f g t)) = span_right (raw_span f g (a*t*b))).
rewrite -(raw_right_image_factorization f g t) -Category.compose_assoc DPMackeyRepresentatives.translated_iso_second.
exact: raw_right_image_factorization.
Qed.

Lemma raw_translate_factor (h : DPFusionSystem.arrow F X (raw_apex f g (a*t*b))) :
    exists h0 : DPFusionSystem.arrow F X (raw_apex f g t),
      orbit_compose (orbit_class h0) (orbit_class (raw_left f g t)) =
        orbit_compose (orbit_class h) (orbit_class (raw_left f g (a*t*b))) /\
      orbit_compose (orbit_class h0) (orbit_class (raw_right f g t)) =
        orbit_compose (orbit_class h) (orbit_class (raw_right f g (a*t*b))).
Proof.
pose tr := @DPMackeyRepresentatives.translated_arrow S F (image (val f)) (image (val g)) a t b Ha Kb.
exists (DPFusionSystem.arrow_compose h tr); split.
- rewrite -orbit_compose_class.
  change (@Category.compose (orbit_category F) _ _ _ (@Category.compose (orbit_category F) _ _ _ (orbit_class h) (iso_hom e))
    (orbit_class (raw_left f g t)) = @Category.compose (orbit_category F) _ _ _ (orbit_class h) (orbit_class (raw_left f g (a*t*b)))).
  by rewrite Category.compose_assoc raw_translated_left.
- rewrite -orbit_compose_class.
  change (@Category.compose (orbit_category F) _ _ _ (@Category.compose (orbit_category F) _ _ _ (orbit_class h) (iso_hom e))
    (orbit_class (raw_right f g t)) = @Category.compose (orbit_category F) _ _ _ (orbit_class h) (orbit_class (raw_right f g (a*t*b)))).
  by rewrite Category.compose_assoc raw_translated_right.
Qed.
End Translation.
End DPFusionCentricPullbackExistence.
