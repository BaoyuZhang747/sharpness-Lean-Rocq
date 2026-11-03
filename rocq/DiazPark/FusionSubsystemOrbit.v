(** The actual orbit functor for a subsystem over a subgroup. Its hypothesis
    is precisely preservation of allowed fusion maps by the subgroup inclusion. *)

From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionCentralizerMaps.
Import DPFusion DPFusionSubgroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionSubsystem.
Section Subsystem.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable C : {group S}.
Local Notation T := [subg C]%type.
Variable H : DPFusionSystem.system [the finGroupType of T].
Hypothesis hH : forall (P Q : {group T}) (f : DPFusion.map P Q),
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (lift f).

Definition ambient_arrow (P Q : {group T}) (f : DPFusionSystem.arrow H P Q) :
    DPFusionSystem.arrow F (ambient P) (ambient Q) := Sub (lift (val f)) (hH (valP f)).

Lemma ambient_identity (P : {group T}) :
    ambient_arrow (DPFusionSystem.arrow_identity H P) = DPFusionSystem.arrow_identity F (ambient P).
Proof.
  apply DPFusionSystem.arrow_ext. intros x hx.
  have hxp := ambient_repr hx.
  have he := ambient_subgK hx.
  rewrite -he. change (lift (DPFusion.identity P) (val (subg C x)) = DPFusion.identity (ambient P) (val (subg C x))).
  by rewrite liftE // !DPFusion.identity_in ?ambient_mem.
Qed.

Lemma ambient_composition (P Q U : {group T})
    (f : DPFusionSystem.arrow H P Q) (g : DPFusionSystem.arrow H Q U) :
    ambient_arrow (DPFusionSystem.arrow_compose f g) =
    DPFusionSystem.arrow_compose (ambient_arrow f) (ambient_arrow g).
Proof.
  apply DPFusionSystem.arrow_ext. intros x hx.
  have hxp := ambient_repr hx. have he := ambient_subgK hx.
  rewrite -he. change (lift (DPFusion.compose (val f) (val g)) (val (subg C x)) =
    DPFusion.compose (lift (val f)) (lift (val g)) (val (subg C x))).
  rewrite DPFusion.compose_in ?ambient_mem // !liftE //.
  - by rewrite DPFusion.compose_in.
  - exact (DPFusion.map_into (val f) hxp).
Qed.

Lemma ambient_related (P Q : {group T}) (f g : DPFusionSystem.arrow H P Q) :
    DPFusionOrbit.target_inner f g ->
    DPFusionOrbit.target_inner (ambient_arrow f) (ambient_arrow g).
Proof.
  move=> /exists_inP[r hr /forall_inP hfg].
  apply/exists_inP. exists (val r). exact (ambient_mem hr).
  apply/forall_inP. intros x hx. apply/eqP.
  have hxp := ambient_repr hx. have he := ambient_subgK hx.
  have hg := eqP (hfg (subg C x) hxp).
  rewrite /DPFusionOrbit.arrow_value /= in hg *.
  rewrite -he !liftE // hg. reflexivity.
Qed.

Definition orbit_map (P Q : {group T}) (f : DPFusionOrbit.orbit_hom H P Q) :
    DPFusionOrbit.orbit_hom F (ambient P) (ambient Q) :=
  DPFusionOrbit.orbit_class (ambient_arrow (repr f)).

Lemma orbit_map_class (P Q : {group T}) (f : DPFusionSystem.arrow H P Q) :
    orbit_map (DPFusionOrbit.orbit_class f) = DPFusionOrbit.orbit_class (ambient_arrow f).
Proof.
  apply/DPFusionOrbit.orbit_class_eq. apply ambient_related.
  exact (DPFusionOrbit.representative_related f).
Qed.

Definition orbit_functor : functor (DPFusionOrbit.orbit_category H) (DPFusionOrbit.orbit_category F).
Proof.
  refine (@Build_functor (DPFusionOrbit.orbit_category H) (DPFusionOrbit.orbit_category F)
    (@ambient S C) (fun P Q f => orbit_map f) _ _).
  - intro P. change (orbit_map (DPFusionOrbit.orbit_class (DPFusionSystem.arrow_identity H P)) =
      DPFusionOrbit.orbit_class (DPFusionSystem.arrow_identity F (ambient P))).
    rewrite orbit_map_class ambient_identity. reflexivity.
  - intros P Q U f g. change (orbit_map (DPFusionOrbit.orbit_compose f g) =
      DPFusionOrbit.orbit_compose (orbit_map f) (orbit_map g)).
    rewrite /DPFusionOrbit.orbit_compose orbit_map_class ambient_composition.
    rewrite /orbit_map. exact (esym (DPFusionOrbit.orbit_compose_class _ _)).
Defined.

Lemma ambient_conjugate (P Q : {group T}) :
    DPFusionSystem.conjugate H P Q -> DPFusionSystem.conjugate F (ambient P) (ambient Q).
Proof.
  move=> /existsP[f /andP[hf /eqP ho]].
  apply/existsP. exists (lift f). apply/andP. split. exact (hH hf).
  apply/eqP. by rewrite lift_image ho.
Qed.

End Subsystem.
End DPFusionSubsystem.
