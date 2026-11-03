From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionConjugacy FusionCentralizerCover FusionCentralizerCoverProjection.
Import DPFusion DPFusionOrbit DPFusionCentralizerCover DPFusionCentralizerCoverProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverIsomorphism.
Section Isomorphism.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Variables X Y : cover_object F p.
Variable f : DPFusionSystem.arrow F (carrier X) (carrier Y).
Hypothesis onto : DPFusion.image (val f) = carrier Y.
Hypothesis eE : DPFusion.map_morphism (val f) @* elementary X = elementary Y.

Lemma forward_condition : raw_condition f.
Proof. by rewrite /raw_condition eE. Qed.
Definition inverse_raw : DPFusionSystem.arrow F (carrier Y) (carrier X) :=
  Sub (DPFusionConjugacy.onto_inverse onto) (DPFusionConjugacy.onto_inverse_allowed onto (valP f)).
Lemma inverse_condition : raw_condition inverse_raw.
Proof.
apply/subsetP=> x Ex.
have Px := subsetP (elementary_sub X) x Ex.
have Ey : val f x \in elementary Y.
  rewrite -eE; apply/morphimP; by exists x.
apply/morphimP; exists (val f x).
- exact (DPFusion.map_into (val f) Px).
- exact Ey.
- exact (esym (DPFusionConjugacy.onto_inverse_cancel onto Px)).
Qed.

Definition raw_cover_iso : @isomorphism (cover_category F p) X Y.
Proof.
refine (@Build_isomorphism (cover_category F p) X Y
  (cover_class forward_condition) (cover_class inverse_condition) _ _).
- apply: val_inj.
  exact: (iso_hom_inv (DPFusionRanks.raw_onto_iso onto)).
- apply: val_inj.
  exact: (iso_inv_hom (DPFusionRanks.raw_onto_iso onto)).
Defined.
End Isomorphism.
End DPFusionCentralizerCoverIsomorphism.
