From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFibration FusionMaps FusionSystems FusionOrbit
  FusionCentralizerCover FusionCentralizerCoverProjection FusionCentralizerCoverFibration.
Import DPFusion DPFusionCentralizerCover DPFusionCentralizerCoverProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Module DPFusionCentralizerCoverFiberEqualities.
Section Equalities.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Variables X Y : centralized_object F p.
Variable B : elementary_object F p.
Variables (eX : projection_object X = B) (eY : projection_object Y = B).
Variable f : cover_hom (val Y) (val X).
Local Notation D := (opposite (opposite (elementary_category F p))).

Lemma delta_fixed_over :
  {in elementary (val X), delta f =1 id} ->
  @Category.compose D _ _ _ (fmap (functor_op (projection F p)) f)
    (@equality_arrow D _ _ eY) = @equality_arrow D _ _ eX.
Proof.
move=> hf; apply: DPFusionSystem.arrow_ext=> x Ex.
cbn [Category.compose opposite elementary_category DPFusionSystem.arrow_compose functor_op projection projection_arrow fmap].
rewrite DPFusion.compose_in // !DPFusionCentralizerCoverFibration.elementary_equality_arrowE
  ?DPFusion.map_into //; exact (hf x Ex).
Qed.

Lemma delta_fixed_of_over :
  @Category.compose D _ _ _ (fmap (functor_op (projection F p)) f)
    (@equality_arrow D _ _ eY) = @equality_arrow D _ _ eX ->
  {in elementary (val X), delta f =1 id}.
Proof.
move=> he x Ex.
have h := congr1 (fun a : DPFusionSystem.arrow F (elementary (val X)) (val B) => val a x) he.
cbn [Category.compose opposite elementary_category DPFusionSystem.arrow_compose functor_op projection projection_arrow fmap] in h.
rewrite DPFusion.compose_in // !DPFusionCentralizerCoverFibration.elementary_equality_arrowE
  ?DPFusion.map_into // in h.
rewrite (@DPFusionCentralizerCoverFibration.elementary_equality_arrowE S F p (projection_object X) B eX x Ex) in h.
exact h.
Qed.
End Equalities.
End DPFusionCentralizerCoverFiberEqualities.




