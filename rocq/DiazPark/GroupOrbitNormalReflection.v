(** The normal-subgroup reflector is defined on actual transporter cosets.
    The intermediate collection interface is discharged for p-subgroups below. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryAdjunction
  GroupOrbitCategory GroupOrbitCollections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPGroupOrbitNormal.
Section Reflection.
Variable G : finGroupType.
Variable N : {group G}.
Hypothesis normalN : N <| [set: G].

Lemma conjugate_normal g : N :^ g = N.
Proof. apply/normP. apply (subsetP (normal_norm normalN)). exact (in_setT g). Qed.

Definition join (H : {group G}) := (H <*> N)%G.
Lemma join_sub (H : {group G}) : H \subset join H.
Proof. exact (joing_subl H N). Qed.
Lemma normal_sub_join (H : {group G}) : N \subset join H.
Proof. exact (joing_subr H N). Qed.
Lemma join_eq (H : {group G}) : N \subset H -> join H = H.
Proof. move=> h. apply val_inj. exact (joing_idPl h). Qed.

Definition join_raw (H K : {group G}) (f : DPGroupOrbit.transporter H K) :
    DPGroupOrbit.transporter (join H) (join K).
Proof.
  exists (val f). rewrite conjYg conjugate_normal join_subG.
  apply/andP; split; last exact (normal_sub_join K).
  exact (subset_trans (valP f) (join_sub K)).
Defined.

Lemma join_related (H K : {group G}) (f g : DPGroupOrbit.transporter H K) :
    DPGroupOrbit.related f g -> DPGroupOrbit.related (join_raw f) (join_raw g).
Proof.
  move/eqP=> h. apply/eqP/lcoset_eqP.
  change (val f \in val g *: join K).
  have hg : val f \in val g *: K by rewrite -h; exact (lcoset_refl _ _).
  move/lcosetP: hg => [k hk ->]. apply/lcosetP; exists k; last reflexivity.
  exact (subsetP (join_sub K) k hk).
Qed.
Definition join_map (H K : {group G}) (f : DPGroupOrbit.orbit_hom H K) :=
  DPGroupOrbit.orbit_class (join_raw (repr f)).
Lemma join_map_class (H K : {group G}) (f : DPGroupOrbit.transporter H K) :
    join_map (DPGroupOrbit.orbit_class f) = DPGroupOrbit.orbit_class (join_raw f).
Proof. apply/DPGroupOrbit.orbit_class_eq. apply join_related. apply DPGroupOrbit.representative_related. Qed.

Lemma join_map_id (H : {group G}) :
    join_map (DPGroupOrbit.orbit_identity H) = DPGroupOrbit.orbit_identity (join H).
Proof. rewrite /DPGroupOrbit.orbit_identity join_map_class. congr (DPGroupOrbit.orbit_class _). apply val_inj. reflexivity. Qed.
Lemma join_map_compose (H K L : {group G})
    (f : DPGroupOrbit.orbit_hom H K) (g : DPGroupOrbit.orbit_hom K L) :
    join_map (DPGroupOrbit.orbit_compose f g) =
      DPGroupOrbit.orbit_compose (join_map f) (join_map g).
Proof.
  move: f g. apply: quotW => f. apply: quotW => g.
  rewrite DPGroupOrbit.orbit_compose_class !join_map_class DPGroupOrbit.orbit_compose_class.
  congr (DPGroupOrbit.orbit_class _). apply val_inj. reflexivity.
Qed.

Variable B : {group G} -> bool.
Hypothesis join_closed : forall H, B H -> B (join H).
Definition contains (H : {group G}) := B H && (N \subset H).
Definition base := DPGroupOrbitCollection.category B.
Definition containing := DPGroupOrbitCollection.category contains.

Definition reflect_object (H : base) : containing.
Proof. exists (join (val H)). apply/andP; split; [exact (join_closed (valP H)) | exact (normal_sub_join (val H))]. Defined.
Definition forget_object (H : containing) : base.
Proof. exists (val H). exact (andP (valP H)).1. Defined.

Definition reflector : functor base containing.
Proof.
  refine (@Build_functor _ _ reflect_object (fun H K f => join_map f) _ _).
  - intro H. exact (join_map_id (val H)).
  - intros H K L f g. exact (join_map_compose f g).
Defined.
Definition inclusion : functor containing base.
Proof. refine (@Build_functor _ _ forget_object (fun H K f => f) _ _); reflexivity. Defined.

Definition inclusion_raw (H K : {group G}) (h : H \subset K) : DPGroupOrbit.transporter H K.
Proof. exists 1. by rewrite conjsg1. Defined.
Definition unit_component (H : base) : hom base H (fobj inclusion (fobj reflector H)) :=
  DPGroupOrbit.orbit_class (inclusion_raw (join_sub (val H))).
Definition counit_component (H : containing) : hom containing (fobj reflector (fobj inclusion H)) H.
Proof.
  apply DPGroupOrbit.orbit_class. apply inclusion_raw.
  rewrite /join join_subG. apply/andP; split; first exact (subxx _).
  exact (andP (valP H)).2.
Defined.

Definition unit : nat_trans (functor_id base) (functor_comp reflector inclusion).
Proof.
  refine (@Build_nat_trans base base (functor_id base)
    (functor_comp reflector inclusion) unit_component _).
  intros H K. apply: quotW => f.
  change (DPGroupOrbit.orbit_compose (DPGroupOrbit.orbit_class f) (unit_component K) =
    DPGroupOrbit.orbit_compose (unit_component H) (join_map (DPGroupOrbit.orbit_class f))).
  rewrite /unit_component join_map_class !DPGroupOrbit.orbit_compose_class.
  congr (DPGroupOrbit.orbit_class _). apply val_inj. by rewrite /= mulg1 mul1g.
Defined.

Definition counit : nat_trans (functor_comp inclusion reflector) (functor_id containing).
Proof.
  refine (@Build_nat_trans containing containing (functor_comp inclusion reflector)
    (functor_id containing) counit_component _).
  intros H K. apply: quotW => f.
  change (DPGroupOrbit.orbit_compose (join_map (DPGroupOrbit.orbit_class f)) (counit_component K) =
    DPGroupOrbit.orbit_compose (counit_component H) (DPGroupOrbit.orbit_class f)).
  rewrite /counit_component join_map_class !DPGroupOrbit.orbit_compose_class.
  congr (DPGroupOrbit.orbit_class _). apply val_inj. by rewrite /= mulg1 mul1g.
Defined.

Definition normal_reflection : adjunction reflector inclusion.
Proof.
  refine (@Build_adjunction _ _ reflector inclusion unit counit _ _).
  - intro H.
    change (DPGroupOrbit.orbit_compose (join_map (unit_component H))
      (counit_component (reflect_object H)) = DPGroupOrbit.orbit_identity (join (val H))).
    rewrite /unit_component /counit_component join_map_class DPGroupOrbit.orbit_compose_class.
    congr (DPGroupOrbit.orbit_class _). apply val_inj. exact (mul1g 1).
  - intro H.
    change (DPGroupOrbit.orbit_compose (unit_component (forget_object H))
      (counit_component H) = DPGroupOrbit.orbit_identity (val H)).
    rewrite /unit_component /counit_component DPGroupOrbit.orbit_compose_class.
    congr (DPGroupOrbit.orbit_class _). apply val_inj. exact (mul1g 1).
Defined.

End Reflection.
End DPGroupOrbitNormal.
