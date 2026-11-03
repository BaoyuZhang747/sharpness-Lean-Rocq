From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSlice
  FusionSystems FusionOrbit FusionFiniteCategory FusionOrbitRanks.
Import DPFusionOrbit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SliceInverse.
Variable C : finite_category.
Variable T : fc_object C.

Definition fc_slice_iso_of_iso (X Y : @fc_slice_object C T)
    (f : fc_slice_hom X Y)
    (e : @isomorphism (fc_category C) (projT1 X) (projT1 Y))
    (he : iso_hom e = val f) :
    @isomorphism (fc_category (@fc_slice C T)) X Y.
Proof.
assert (hi : fc_compose (iso_inv e) (projT2 X) == projT2 Y).
{
  apply/eqP; rewrite -(eqP (valP f)) -he -fc_assoc.
  have h := iso_inv_hom e.
  change (fc_compose (iso_inv e) (iso_hom e) = fc_identity (projT1 Y)) in h.
  by rewrite h fc_id_left.
}
refine (@Build_isomorphism (fc_category (@fc_slice C T)) X Y f
  (Sub (iso_inv e) hi) _ _).
- apply: val_inj.
  change (fc_compose (val f) (iso_inv e) = fc_identity (projT1 X)).
  rewrite -he; exact (iso_hom_inv e).
- apply: val_inj.
  change (fc_compose (iso_inv e) (val f) = fc_identity (projT1 Y)).
  rewrite -he; exact (iso_inv_hom e).
Defined.

Lemma fc_slice_iso_of_iso_hom X Y f e he :
    iso_hom (@fc_slice_iso_of_iso X Y f e he) = f.
Proof. reflexivity. Qed.

End SliceInverse.

Module DPBurnsideFusionRanks.
Section FusionRanks.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition centric_rank (P : fc_object (DPFusionFinite.centric_finite_category F)) :=
  #|val P|.

Lemma centric_rank_le P Q
    (f : fc_hom (DPFusionFinite.centric_finite_category F) P Q) :
    centric_rank P <= centric_rank Q.
Proof. exact (DPFusionRanks.orbit_rank_le f). Qed.

Definition centric_equal_rank_iso P Q
    (f : fc_hom (DPFusionFinite.centric_finite_category F) P Q)
    (h : centric_rank P = centric_rank Q) :
    @isomorphism (fc_category (DPFusionFinite.centric_finite_category F)) P Q.
Proof.
pose e := DPFusionRanks.orbit_equal_rank_iso f h.
refine (@Build_isomorphism (fc_category (DPFusionFinite.centric_finite_category F))
  P Q (iso_hom e) (iso_inv e) _ _).
- exact (iso_hom_inv e).
- exact (iso_inv_hom e).
Defined.

Lemma centric_equal_rank_iso_hom P Q f h :
    iso_hom (@centric_equal_rank_iso P Q f h) = f.
Proof. exact: DPFusionRanks.orbit_equal_rank_iso_hom. Qed.

Variable T : fc_object (DPFusionFinite.centric_finite_category F).

Definition centric_slice_rank
    (X : fc_object (@fc_slice (DPFusionFinite.centric_finite_category F) T)) :=
  centric_rank (projT1 X).

Lemma centric_slice_rank_le X Y
    (f : fc_hom (@fc_slice (DPFusionFinite.centric_finite_category F) T) X Y) :
    centric_slice_rank X <= centric_slice_rank Y.
Proof. exact: centric_rank_le (val f). Qed.

Definition centric_slice_equal_rank_iso X Y
    (f : fc_hom (@fc_slice (DPFusionFinite.centric_finite_category F) T) X Y)
    (h : centric_slice_rank X = centric_slice_rank Y) :
    @isomorphism (fc_category (@fc_slice (DPFusionFinite.centric_finite_category F) T)) X Y :=
  fc_slice_iso_of_iso (centric_equal_rank_iso_hom (val f) h).

Lemma centric_slice_equal_rank_iso_hom X Y f h :
    iso_hom (@centric_slice_equal_rank_iso X Y f h) = f.
Proof. reflexivity. Qed.

End FusionRanks.
End DPBurnsideFusionRanks.

Print Assumptions fc_slice_iso_of_iso.
Print Assumptions DPBurnsideFusionRanks.centric_slice_equal_rank_iso.
Print Assumptions DPBurnsideFusionRanks.centric_slice_equal_rank_iso_hom.
