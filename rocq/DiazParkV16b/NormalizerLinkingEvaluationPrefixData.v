(** Concrete universal image-prefix data in the actual evaluation comma.
    The full-image case is the unchanged chain with its actual structural isomorphism. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemIsomorphisms LinkingChainObjects
  NormalizerLinkingChainCategory NormalizerLinkingChainEvaluation
  NormalizerLinkingEvaluationImage NormalizerLinkingEvaluationPoints.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingIsomorphisms DPLinkingChains DPNormalizerLinkingChainCategory
  DPNormalizerLinkingChainEvaluation DPNormalizerLinkingEvaluationImage DPNormalizerLinkingEvaluationPoints.

Module DPNormalizerLinkingEvaluationPrefixData.
Section Data.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation C := (chain_category L).
Local Notation D := (linking_category L).
Local Notation E := (evaluation L).
Local Notation UC := (evaluation_under L P).
Local Notation PT := (evaluation_points L P).
Local Notation J := (points_inclusion L P).

Record prefix_data (X : UC) := {
  prefix_point : PT;
  prefix_deletion : hom UC (point_under prefix_point) X;
  prefix_universal : forall (Y : PT) (f : hom UC (point_under Y) X),
    exists! g : hom PT Y prefix_point,
      @Category.compose UC _ _ _ (fmap J g) prefix_deletion = f
}.

Section FullImage.
Variable X : UC.
Hypothesis he : DPFusion.image (val (linking_projection L (costructured_arrow X))) =
  val (fobj E (costructured_source X)).

Definition full_point : PT := @Build_evaluation_point S F L P (costructured_source X)
  (@isomorphism_of_image_eq S F L P (fobj E (costructured_source X)) (costructured_arrow X) he).

Definition full_deletion : hom UC (point_under full_point) X.
Proof.
refine (@Build_costructured_hom (opposite C) (opposite D) (functor_op E) P
  X (point_under full_point) (@Category.identity C (costructured_source X)) _).
change (@Category.compose D _ _ _ (costructured_arrow X)
  (fmap E (@Category.identity C (costructured_source X))) = costructured_arrow X).
by rewrite fmap_id compose_id_right.
Defined.

Definition full_lift (Y : PT) (f : hom UC (point_under Y) X) : hom PT Y full_point.
Proof.
refine (@Build_costructured_hom (opposite C) (opposite D) (functor_op E) P
  (point_under full_point) (point_under Y) (costructured_map f) _).
exact (costructured_commutes f).
Defined.

Lemma full_lift_spec (Y : PT) (f : hom UC (point_under Y) X) :
  @Category.compose UC _ _ _ (fmap J (full_lift f)) full_deletion = f.
Proof.
apply costructured_hom_ext.
change (@Category.compose C _ _ _ (costructured_map f)
  (@Category.identity C (costructured_source X)) = costructured_map f).
exact: compose_id_right.
Qed.

Lemma full_lift_unique (Y : PT) (f : hom UC (point_under Y) X)
    (g : hom PT Y full_point)
    (hg : @Category.compose UC _ _ _ (fmap J g) full_deletion = f) : full_lift f = g.
Proof.
apply costructured_hom_ext.
have h := f_equal (@costructured_map (opposite C) (opposite D) (functor_op E) P
  X (point_under Y)) hg.
change (@Category.compose C _ _ _ (costructured_map g)
  (@Category.identity C (costructured_source X)) = costructured_map f) in h.
rewrite compose_id_right in h; exact: esym h.
Qed.

Definition full_image_data : prefix_data X.
Proof.
refine (@Build_prefix_data X full_point full_deletion _)=> Y f.
exists (full_lift f); split; [exact: full_lift_spec | exact: full_lift_unique].
Defined.
End FullImage.
End Data.
End DPNormalizerLinkingEvaluationPrefixData.
