From mathcomp Require Import all_boot all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionConjugacy FusionMackeyShape.
Import DPFusion DPFusionSystem DPFusionOrbit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionRanks.
Section Ranks.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma raw_rank_le (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
    (#|P| <= #|Q|)%N.
Proof.
rewrite -(DPFusionConjugacy.map_image_card (val f)).
exact: subset_leq_card (DPFusion.image_sub (val f)).
Qed.

Lemma orbit_rank_le (P Q : {group S}) (f : DPFusionOrbit.orbit_hom F P Q) :
    (#|P| <= #|Q|)%N.
Proof. exact: raw_rank_le (repr f). Qed.

Lemma raw_equal_rank_image (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
    #|P| = #|Q| -> DPFusion.image (val f) = Q.
Proof.
move=> h; apply: val_inj; apply/eqP.
by rewrite eqEcard DPFusion.image_sub DPFusionConjugacy.map_image_card h leqnn.
Qed.

Lemma orbit_equal_rank_conjugate (P Q : {group S}) (f : DPFusionOrbit.orbit_hom F P Q) :
    #|P| = #|Q| -> DPFusionSystem.conjugate F P Q.
Proof.
move=> h; apply/existsP; exists (val (repr f)); apply/andP; split.
- exact: valP (repr f).
- apply/eqP; exact: raw_equal_rank_image h.
Qed.

Definition raw_onto_iso (P Q : {group S}) (f : DPFusionSystem.arrow F P Q)
    (onto : DPFusion.image (val f) = Q) :
    @isomorphism (DPFusionOrbit.orbit_category F) P Q.
Proof.
pose invf : DPFusionSystem.arrow F Q P := Sub (DPFusionConjugacy.onto_inverse onto)
  (DPFusionConjugacy.onto_inverse_allowed onto (valP f)).
refine (@Build_isomorphism (DPFusionOrbit.orbit_category F) P Q
  (DPFusionOrbit.orbit_class f) (DPFusionOrbit.orbit_class invf) _ _).
- cbn [Category.compose Category.identity DPFusionOrbit.orbit_category].
  rewrite DPFusionOrbit.orbit_compose_class.
  apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Px.
  rewrite /DPFusionSystem.arrow_compose /DPFusionSystem.arrow_identity /=.
  by rewrite DPFusion.compose_in // DPFusionConjugacy.onto_inverse_cancel // DPFusion.identity_in.
- cbn [Category.compose Category.identity DPFusionOrbit.orbit_category].
  rewrite DPFusionOrbit.orbit_compose_class.
  apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Qx.
  rewrite /DPFusionSystem.arrow_compose /DPFusionSystem.arrow_identity /=.
  by rewrite DPFusion.compose_in // DPFusionConjugacy.onto_inverse_cancel_right // DPFusion.identity_in.
Defined.

Definition orbit_equal_rank_iso (P Q : {group S}) (f : DPFusionOrbit.orbit_hom F P Q)
    (h : #|P| = #|Q|) : @isomorphism (DPFusionOrbit.orbit_category F) P Q :=
  raw_onto_iso (raw_equal_rank_image (repr f) h).

Lemma orbit_equal_rank_iso_hom (P Q : {group S}) (f : DPFusionOrbit.orbit_hom F P Q)
    (h : #|P| = #|Q|) : iso_hom (orbit_equal_rank_iso f h) = f.
Proof. exact: reprK. Qed.

End Ranks.
End DPFusionRanks.

Print Assumptions DPFusionRanks.orbit_rank_le.
Print Assumptions DPFusionRanks.orbit_equal_rank_iso.
Print Assumptions DPFusionRanks.orbit_equal_rank_iso_hom.
