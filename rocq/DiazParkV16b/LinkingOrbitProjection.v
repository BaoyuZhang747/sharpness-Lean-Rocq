(** The actual linking-to-centric-orbit projection and chosen lifts of
    orbit arrows.  The quotient is the existing target-inner quotient. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem LinkingSystemFinite.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingFinite.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPLinkingOrbit.
Section Projection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition orbit_projection : functor (linking_category L) (DPFusionOrbit.centric_orbit_category F).
Proof.
refine (@Build_functor (linking_category L) (DPFusionOrbit.centric_orbit_category F)
  (fun P => P) (fun P Q f => DPFusionOrbit.orbit_class (linking_projection L f)) _ _).
- move=> P; by rewrite projection_identity.
- move=> P Q R f g; rewrite projection_compose; exact: esym (DPFusionOrbit.orbit_compose_class _ _).
Defined.

Lemma orbit_projection_object (P : Obj) : fobj orbit_projection P = P.
Proof. reflexivity. Qed.

Lemma orbit_projection_map (P Q : Obj) (f : linking_hom L P Q) :
    fmap orbit_projection f = DPFusionOrbit.orbit_class (linking_projection L f).
Proof. reflexivity. Qed.

Lemma orbit_projection_distinguished (P : Obj) (x : [subg (val P)]) :
    fmap orbit_projection (distinguished L x) =
    @identity (DPFusionOrbit.centric_orbit_category F) P.
Proof.
apply esym; apply/DPFusionOrbit.orbit_class_eq/exists_inP.
exists (val x); first exact: valP.
apply/forall_inP=> y Py; apply/eqP.
rewrite /DPFusionOrbit.arrow_value /distinguished projection_transporter /=.
by rewrite DPFusion.conjugation_in // DPFusion.identity_in.
Qed.

Definition lift_orbit_arrow (P Q : Obj)
    (a : hom (DPFusionOrbit.centric_orbit_category F) P Q) : linking_hom L P Q :=
  chosen_lift L (repr a).

Lemma orbit_projection_lift (P Q : Obj)
    (a : hom (DPFusionOrbit.centric_orbit_category F) P Q) :
    fmap orbit_projection (lift_orbit_arrow a) = a.
Proof.
rewrite orbit_projection_map /lift_orbit_arrow chosen_lift_projection.
exact: reprK.
Qed.

Theorem orbit_projection_surjective (P Q : Obj)
    (a : hom (DPFusionOrbit.centric_orbit_category F) P Q) :
    exists f : linking_hom L P Q, fmap orbit_projection f = a.
Proof. exists (lift_orbit_arrow a); exact: orbit_projection_lift. Qed.
End Projection.
End DPLinkingOrbit.

Check DPLinkingOrbit.orbit_projection.
Check DPLinkingOrbit.orbit_projection_surjective.
Print Assumptions DPLinkingOrbit.orbit_projection_distinguished.
Print Assumptions DPLinkingOrbit.orbit_projection_surjective.
