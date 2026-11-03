(** Actual isomorphism-pointed objects in the structured evaluation comma. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryComma FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainRestrictionMaps
  NormalizerLinkingChainCategory NormalizerLinkingChainEvaluation.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainRestrictionMaps
  DPNormalizerLinkingChainCategory DPNormalizerLinkingChainEvaluation.

Module DPNormalizerLinkingEvaluationPoints.
Section Points.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.

Definition evaluation_under := structured_category (evaluation L) P.

Record evaluation_point := {
  point_chain : chain F;
  point_iso : @isomorphism (linking_category L) P (fobj (evaluation L) point_chain)
}.

Definition point_under (x : evaluation_point) : evaluation_under :=
  @Build_costructured_object (opposite (chain_category L)) (opposite (linking_category L))
    (functor_op (evaluation L)) P (point_chain x) (iso_hom (point_iso x)).

Definition evaluation_points : category.
Proof.
refine (@Build_category evaluation_point
  (fun x y => hom evaluation_under (point_under x) (point_under y))
  (fun x => @identity evaluation_under (point_under x))
  (fun x y z f g => @compose evaluation_under _ _ _ f g) _ _ _).
- intros; exact: compose_id_left.
- intros; exact: compose_id_right.
- intros; exact: compose_assoc.
Defined.

Definition points_inclusion : functor evaluation_points evaluation_under.
Proof.
refine (@Build_functor evaluation_points evaluation_under point_under
  (fun x y f => f) _ _); reflexivity.
Defined.

Definition point_map (x y : evaluation_points) (f : hom evaluation_points x y) :
  chain_map L (point_chain x) (point_chain y) := costructured_map f.

Lemma point_map_square (x y : evaluation_points) (f : hom evaluation_points x y) :
  linking_compose L (iso_hom (point_iso x)) (evaluation_arrow (point_map f)) =
  iso_hom (point_iso y).
Proof. exact (costructured_commutes f). Qed.

Lemma point_under_chain (x : evaluation_point) : costructured_source (point_under x) = point_chain x.
Proof. reflexivity. Qed.

Lemma point_under_arrow (x : evaluation_point) : costructured_arrow (point_under x) = iso_hom (point_iso x).
Proof. reflexivity. Qed.

End Points.
End DPNormalizerLinkingEvaluationPoints.
