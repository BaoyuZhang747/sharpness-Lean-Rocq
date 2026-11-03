From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryAdjunction FusionSystems FusionSaturation
  FusionCentralizerCover FusionCentralizerCoverNormalization.
Import DPFusionCentralizerCover DPFusionCentralizerCoverNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPFusionCentralizerCoverEquivalence.
Section Equivalence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.

Local Notation C := (cover_category F p).
Local Notation D := (centralized_category F p).
Local Notation I := (centralized_inclusion F p).
Variable r : C -> D.
Variable e : forall X : C, @isomorphism C X (val (r X)).


Definition normalizing_functor : functor C D.
Proof.
refine (@Build_functor C D r
  (fun X Y f => Category.compose (iso_inv (e X)) (Category.compose f (iso_hom (e Y)))) _ _).
- move=> X; change (Category.compose (iso_inv (e X))
    (Category.compose (@Category.identity C X) (iso_hom (e X))) = @Category.identity C (val (r X))).
  rewrite compose_id_left; exact: iso_inv_hom.
- move=> X Y Z f g.
  change (Category.compose (iso_inv (e X)) (Category.compose (Category.compose f g) (iso_hom (e Z))) =
    Category.compose (Category.compose (iso_inv (e X)) (Category.compose f (iso_hom (e Y))))
      (Category.compose (iso_inv (e Y)) (Category.compose g (iso_hom (e Z))))).
  rewrite !compose_assoc -(compose_assoc (iso_hom (e Y)) (iso_inv (e Y)))
    iso_hom_inv compose_id_left; reflexivity.
Defined.

Definition normalization_unit : nat_trans (functor_id C) (functor_comp normalizing_functor I).
Proof.
refine (@Build_nat_trans C C (functor_id C) (functor_comp normalizing_functor I)
  (fun X => iso_hom (e X)) _).
move=> X Y f.
change (Category.compose f (iso_hom (e Y)) =
  Category.compose (iso_hom (e X))
    (Category.compose (iso_inv (e X)) (Category.compose f (iso_hom (e Y))))).
by rewrite -compose_assoc iso_hom_inv compose_id_left.
Defined.

Definition normalization_counit : nat_trans (functor_comp I normalizing_functor) (functor_id D).
Proof.
refine (@Build_nat_trans D D (functor_comp I normalizing_functor) (functor_id D)
  (fun X => iso_inv (e (val X))) _).
move=> X Y f.
change (Category.compose
  (Category.compose (iso_inv (e (val X))) (Category.compose f (iso_hom (e (val Y)))))
  (iso_inv (e (val Y))) = Category.compose (iso_inv (e (val X))) f).
by rewrite !compose_assoc iso_hom_inv compose_id_right.
Defined.

Definition normalization_adjunction : adjunction normalizing_functor I.
Proof.
refine (@Build_adjunction C D normalizing_functor I normalization_unit normalization_counit _ _).
- move=> X.
  change (Category.compose
    (Category.compose (iso_inv (e X)) (Category.compose (iso_hom (e X)) (iso_hom (e (val (r X))))))
    (iso_inv (e (val (r X)))) = @Category.identity C (val (r X))).
  rewrite -[Category.compose (iso_inv (e X)) _]compose_assoc iso_inv_hom compose_id_left.
  exact: iso_hom_inv.
- move=> X; exact: iso_hom_inv.
Defined.

Definition normalization_unit_iso (X : C) :
    @isomorphism C X (fobj I (fobj normalizing_functor X)) := e X.
Definition normalization_counit_iso (X : D) :
    @isomorphism D (fobj normalizing_functor (fobj I X)) X.
Proof.
refine (@Build_isomorphism D _ _ (iso_inv (e (val X))) (iso_hom (e (val X))) _ _).
- exact (@iso_inv_hom C _ _ (e (val X))).
- exact (@iso_hom_inv C _ _ (e (val X))).
Defined.
End Equivalence.

Section ActualEquivalence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.

Definition centralized_retraction :
  functor (cover_category F p) (centralized_category F p) :=
  @normalizing_functor S F p (normalized_object sat) (normalization_iso sat).

Definition centralized_inclusion_right_adjoint :
  adjunction centralized_retraction (centralized_inclusion F p) :=
  @normalization_adjunction S F p (normalized_object sat) (normalization_iso sat).

Definition centralized_unit_iso (X : cover_object F p) :
  @isomorphism (cover_category F p) X
    (fobj (centralized_inclusion F p) (fobj centralized_retraction X)) :=
  normalization_iso sat X.

Definition centralized_counit_iso (X : centralized_object F p) :
  @isomorphism (centralized_category F p)
    (fobj centralized_retraction (fobj (centralized_inclusion F p) X)) X :=
  @normalization_counit_iso S F p (normalized_object sat) (normalization_iso sat) X.
End ActualEquivalence.
End DPFusionCentralizerCoverEquivalence.





