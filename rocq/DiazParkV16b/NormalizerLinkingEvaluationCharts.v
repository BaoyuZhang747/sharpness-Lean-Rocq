(** Equality charts for prefix-entry linking isomorphisms and their squares. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryAdjointUniqueness FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem NormalizerLinkingEvaluationPrefix.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPNormalizerLinkingEvaluationPrefix.

Module DPNormalizerLinkingEvaluationCharts.
Section Charts.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition chart_iso (P Q P' Q' : Obj) (hP : P = P') (hQ : Q = Q')
    (a : @isomorphism (linking_category L) P' Q') :
    @isomorphism (linking_category L) P Q :=
  isomorphism_composition (object_equality_iso L hP)
    (isomorphism_composition a (object_equality_iso L (esym hQ))).

Lemma chart_iso_square (P Q U V P' Q' U' V' : Obj)
    (hP : P = P') (hQ : Q = Q') (hU : U = U') (hV : V = V')
    (a : @isomorphism (linking_category L) P' U')
    (b : @isomorphism (linking_category L) Q' V')
    (hPQ : val P \subset val Q) (hUV : val U \subset val V)
    (hPQ' : val P' \subset val Q') (hUV' : val U' \subset val V') :
  linking_compose L (inclusion L hPQ') (iso_hom b) =
    linking_compose L (iso_hom a) (inclusion L hUV') ->
  linking_compose L (inclusion L hPQ) (iso_hom (chart_iso hQ hV b)) =
    linking_compose L (iso_hom (chart_iso hP hU a)) (inclusion L hUV).
Proof.
case: P' / hP in a hPQ' *.
case: Q' / hQ in b hPQ' *.
case: U' / hU in a hUV' *.
case: V' / hV in b hUV' *.
have -> : hPQ' = hPQ := Prop_irrelevance _ _.
have -> : hUV' = hUV := Prop_irrelevance _ _.
rewrite /chart_iso /object_equality_iso /isomorphism_composition /=.
by rewrite !linking_id_left !linking_id_right.
Qed.
End Charts.
End DPNormalizerLinkingEvaluationCharts.
