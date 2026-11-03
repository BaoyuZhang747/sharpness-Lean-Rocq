(** Actual restrictions to centric source and target subgroups, derived
    from the linking axioms and uniquely characterized by their square. *)
From mathcomp Require Import all_boot all_fingroup center.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemCancellation LinkingSystemFactorization.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingCancellation DPLinkingFactorization.
Local Open Scope group_scope.

Module DPLinkingRestrictions.
Section Restrictions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).
Variables P Q P0 Q0 : Obj.
Variable f : linking_hom L P Q.
Hypothesis hP : val P0 \subset val P.
Hypothesis hQ : val Q0 \subset val Q.
Hypothesis hImage : DPFusion.image (DPFusion.restrict (val (linking_projection L f)) hP)
  \subset val Q0.

Definition raw_restriction : DPFusionSystem.arrow F (val P0) (val Q0) :=
  Sub (DPFusion.corestrict hImage)
    (DPFusionSystem.corestriction_allowed hImage
      (DPFusionSystem.restriction_allowed hP (valP (linking_projection L f)))).

Lemma restriction_triangle :
    DPFusionSystem.arrow_compose raw_restriction (linking_projection L (inclusion L hQ)) =
    linking_projection L (linking_compose L (inclusion L hP) f).
Proof.
rewrite projection_compose.
have hp := @projection_inclusion S F L P0 P hP.
have hq := @projection_inclusion S F L Q0 Q hQ.
change (val (linking_projection L (inclusion L hP)) = DPFusion.inclusion hP) in hp.
change (val (linking_projection L (inclusion L hQ)) = DPFusion.inclusion hQ) in hq.
apply val_inj.
change (DPFusion.compose (DPFusion.corestrict hImage) (val (linking_projection L (inclusion L hQ))) =
  DPFusion.compose (val (linking_projection L (inclusion L hP))) (val (linking_projection L f))).
rewrite hp hq; apply DPFusion.map_ext => x Px.
rewrite !DPFusion.compose_in //.
rewrite !DPFusion.inclusion_in ?DPFusion.map_into // DPFusion.corestrict_in // DPFusion.restrict_in //.
Qed.

Definition restriction : linking_hom L P0 Q0 := factorization restriction_triangle.

Theorem restriction_projection : linking_projection L restriction = raw_restriction.
Proof. exact: factorization_projection. Qed.

Theorem restriction_square :
    linking_compose L restriction (inclusion L hQ) = linking_compose L (inclusion L hP) f.
Proof. exact: factorization_commutes. Qed.

Theorem restriction_unique (g : linking_hom L P0 Q0) :
    linking_compose L g (inclusion L hQ) = linking_compose L (inclusion L hP) f ->
    g = restriction.
Proof.
move=> hg; apply: (@compose_right_injective S F L P0 Q0 Q (inclusion L hQ)).
by rewrite hg restriction_square.
Qed.
End Restrictions.
End DPLinkingRestrictions.

Check DPLinkingRestrictions.restriction.
Check DPLinkingRestrictions.restriction_square.
Check DPLinkingRestrictions.restriction_unique.
Print Assumptions DPLinkingRestrictions.restriction_square.
Print Assumptions DPLinkingRestrictions.restriction_unique.
