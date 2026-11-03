(** Actual conjugation identifies the two intersection-apex conventions. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionOrbitRanks FusionMackeyShape.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionMackey DPFusionRanks.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPGroupCohomologyMackeyDoubleCosetGeometry.
Section Geometry.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q : {group S}.
Variable t : S.
Definition native_apex : {group S} := (Q :&: P :^ t)%G.

Lemma native_apex_sub : native_apex \subset Q.
Proof. exact: subsetIl. Qed.

Lemma native_apex_conjugate : native_apex :^ t^-1 = inclusion_apex P Q t.
Proof. by rewrite /native_apex /inclusion_apex conjIg conjsgK setIC. Qed.

Lemma native_to_canonical_sub : native_apex :^ t^-1 \subset inclusion_apex P Q t.
Proof. by rewrite native_apex_conjugate. Qed.

Definition apex_arrow : DPFusionSystem.arrow F native_apex (inclusion_apex P Q t) :=
  Sub (conjugation native_to_canonical_sub)
    (DPFusionSystem.conjugation_closed F native_to_canonical_sub).

Lemma apex_equal_rank : #|native_apex| = #|inclusion_apex P Q t|.
Proof. by rewrite -native_apex_conjugate cardJg. Qed.

Definition apex_iso := raw_onto_iso (raw_equal_rank_image apex_arrow apex_equal_rank).

Lemma native_left_sub : native_apex :^ t^-1 \subset P.
Proof. rewrite native_apex_conjugate; exact: inclusion_apex_left. Qed.

Definition native_left : DPFusionSystem.arrow F native_apex P :=
  Sub (conjugation native_left_sub) (DPFusionSystem.conjugation_closed F native_left_sub).
Definition native_right : DPFusionSystem.arrow F native_apex Q :=
  inclusion_arrow F native_apex_sub.

Lemma apex_iso_left :
  Category.compose (iso_hom apex_iso) (DPFusionOrbit.orbit_class (inclusion_left F P Q t)) =
    DPFusionOrbit.orbit_class native_left.
Proof.
change (DPFusionOrbit.orbit_compose (DPFusionOrbit.orbit_class apex_arrow)
  (DPFusionOrbit.orbit_class (inclusion_left F P Q t)) = DPFusionOrbit.orbit_class native_left).
rewrite DPFusionOrbit.orbit_compose_class.
apply congr1; apply val_inj; apply DPFusion.map_ext=> x hx.
change (DPFusion.compose (conjugation native_to_canonical_sub)
  (inclusion (inclusion_apex_left P Q t)) x = conjugation native_left_sub x).
rewrite compose_in // inclusion_in ?map_into // !conjugation_in //.
Qed.

Lemma apex_iso_right :
  Category.compose (iso_hom apex_iso) (DPFusionOrbit.orbit_class (inclusion_right F P Q t)) =
    DPFusionOrbit.orbit_class native_right.
Proof.
change (DPFusionOrbit.orbit_compose (DPFusionOrbit.orbit_class apex_arrow)
  (DPFusionOrbit.orbit_class (inclusion_right F P Q t)) = DPFusionOrbit.orbit_class native_right).
rewrite DPFusionOrbit.orbit_compose_class.
apply congr1; apply val_inj; apply DPFusion.map_ext=> x hx.
change (DPFusion.compose (conjugation native_to_canonical_sub)
  (conjugation (inclusion_apex_right P Q t)) x = inclusion native_apex_sub x).
rewrite compose_in // conjugation_in ?map_into // conjugation_in // inclusion_in //.
exact: conjgKV.
Qed.

End Geometry.
End DPGroupCohomologyMackeyDoubleCosetGeometry.
