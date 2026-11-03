From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionCentralizerMaps FusionSubsystemOrbit.
Import DPFusion DPFusionSubgroup DPFusionSubsystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionSubsystemFaithful.
Section Faithful.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable C : {group S}.
Local Notation T := [subg C]%type.
Variable H : DPFusionSystem.system [the finGroupType of T].
Hypothesis hH : forall (P Q : {group T}) (f : DPFusion.map P Q),
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (lift f).

Lemma ambient_related_reflect (P Q : {group T}) (f g : DPFusionSystem.arrow H P Q) :
  DPFusionOrbit.target_inner (ambient_arrow hH f) (ambient_arrow hH g) ->
  DPFusionOrbit.target_inner f g.
Proof.
move=> /exists_inP[r Qr /forall_inP he].
apply/exists_inP; exists (subg C r); first exact: ambient_repr Qr.
apply/forall_inP=> x Px; apply/eqP/val_inj.
have h := eqP (he (val x) (ambient_mem Px)).
change (lift (val g) (val x) = (lift (val f) (val x)) ^ r) in h.
rewrite !liftE // in h.
change (val (val g x) = (val (val f x)) ^ val (subg C r)).
by rewrite (ambient_subgK Qr).
Qed.

Lemma orbit_map_injective (P Q : {group T}) :
  injective (@orbit_map S F C H hH P Q).
Proof.
move=> f g he.
have hr : DPFusionOrbit.target_inner (repr f) (repr g).
  apply: ambient_related_reflect; apply/DPFusionOrbit.orbit_class_eq; exact he.
have h : DPFusionOrbit.orbit_class (repr f) = DPFusionOrbit.orbit_class (repr g) by apply/DPFusionOrbit.orbit_class_eq.
by rewrite /DPFusionOrbit.orbit_class !reprK in h.
Qed.
End Faithful.
End DPFusionSubsystemFaithful.


