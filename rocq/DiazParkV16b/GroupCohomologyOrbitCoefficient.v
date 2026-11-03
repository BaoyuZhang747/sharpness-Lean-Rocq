(** Native ordinary group cohomology descends to the actual fusion
    orbit category.  Inner invariance comes from the constructed prism,
    independently of transfer or any sharpness theorem. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyInner LinkingCommaNaturality.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPGroupCohomologyFunctor DPLinkingCommaNaturality.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPGroupCohomologyOrbitCoefficient.

Lemma group_morphism_ext (G H : finGroupType) (f g : {morphism [set: G] >-> H}) :
    f =1 g -> f = g.
Proof.
case: f => f hf; case: g => g hg /= h.
have he : f = g by apply functional_extensionality_dep.
subst g; f_equal; apply Prop_irrelevance.
Qed.

Section RawFunctor.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma arrow_group_identity (P : {group S}) :
    arrow_group_hom (DPFusionSystem.arrow_identity F P) = group_hom_identity [subg P]%type.
Proof.
apply group_morphism_ext=> x; apply val_inj.
exact: DPFusion.identity_in (valP x).
Qed.

Lemma arrow_group_compose (P Q T : {group S})
    (a : DPFusionSystem.arrow F P Q) (b : DPFusionSystem.arrow F Q T) :
    arrow_group_hom (DPFusionSystem.arrow_compose a b) =
    group_hom_comp (arrow_group_hom a) (arrow_group_hom b).
Proof.
apply group_morphism_ext=> x; apply val_inj.
exact: DPFusion.compose_in (valP x).
Qed.

Section Coefficients.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Definition value (P : {group S}) : lmodType R := DPGroupCohomology.value R [subg P]%type A n.

Definition raw_pull (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
    module_hom (value Q) (value P) :=
  DPGroupCohomologyPullback.pull A (arrow_group_hom a) n.

Lemma raw_pull_identity (P : {group S}) :
    raw_pull (DPFusionSystem.arrow_identity F P) = module_hom_id (value P).
Proof. rewrite /raw_pull arrow_group_identity; exact: DPGroupCohomologyPullback.pull_identity. Qed.

Lemma raw_pull_compose (P Q T : {group S})
    (a : DPFusionSystem.arrow F P Q) (b : DPFusionSystem.arrow F Q T) :
    raw_pull (DPFusionSystem.arrow_compose a b) = module_hom_comp (raw_pull b) (raw_pull a).
Proof. rewrite /raw_pull arrow_group_compose; exact: DPGroupCohomologyPullback.pull_composition. Qed.

Lemma raw_pull_inner (P Q : {group S}) (a b : DPFusionSystem.arrow F P Q) :
    DPFusionOrbit.target_inner a b -> raw_pull b = raw_pull a.
Proof.
move=> /exists_inP[r Qr /forall_inP hr].
pose rQ : [subg Q] := Sub r Qr.
have hb : arrow_group_hom b = group_hom_comp (arrow_group_hom a) (group_conjugation rQ).
  apply group_morphism_ext=> x; apply val_inj.
  exact: eqP (hr (val x) (valP x)).
rewrite /raw_pull hb DPGroupCohomologyPullback.pull_composition DPGroupCohomologyInner.pull_inner.
apply module_hom_ext=> q; reflexivity.
Qed.

Definition orbit_pull (P Q : {group S}) (a : DPFusionOrbit.orbit_hom F P Q) :
    module_hom (value Q) (value P) := raw_pull (repr a).

Lemma orbit_pull_class (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
    orbit_pull (DPFusionOrbit.orbit_class a) = raw_pull a.
Proof. symmetry; exact: raw_pull_inner (DPFusionOrbit.representative_related a). Qed.

Lemma orbit_pull_identity (P : {group S}) :
    orbit_pull (DPFusionOrbit.orbit_identity F P) = module_hom_id (value P).
Proof. rewrite /DPFusionOrbit.orbit_identity orbit_pull_class; exact: raw_pull_identity. Qed.

Lemma orbit_pull_compose (P Q T : {group S})
    (a : DPFusionOrbit.orbit_hom F P Q) (b : DPFusionOrbit.orbit_hom F Q T) :
    orbit_pull (DPFusionOrbit.orbit_compose a b) = module_hom_comp (orbit_pull b) (orbit_pull a).
Proof.
move: a; apply: quotW=> a; move: b; apply: quotW=> b.
rewrite DPFusionOrbit.orbit_compose_class !orbit_pull_class; exact: raw_pull_compose.
Qed.

Definition coefficient : module_codiagram R (DPFusionOrbit.orbit_category F).
Proof.
refine (@Build_functor (opposite (DPFusionOrbit.orbit_category F)) (module_category R)
  value (fun P Q a => orbit_pull a) _ _).
- exact: orbit_pull_identity.
- move=> P Q T a b; exact: orbit_pull_compose.
Defined.

Definition centric_coefficient : module_codiagram R (DPFusionOrbit.centric_orbit_category F) :=
  functor_comp (functor_op (DPFusionOrbit.centric_inclusion F)) coefficient.

Lemma centric_coefficient_object (P : DPFusionOrbit.centric_object F) :
    fobj centric_coefficient P = DPGroupCohomology.value R [subg (val P)]%type A n.
Proof. reflexivity. Qed.

Lemma centric_coefficient_map (P Q : DPFusionOrbit.centric_object F)
    (a : DPFusionSystem.arrow F (val P) (val Q)) :
    @fmap _ _ centric_coefficient Q P (DPFusionOrbit.orbit_class a) =
    DPGroupCohomologyPullback.pull A (arrow_group_hom a) n.
Proof. exact: orbit_pull_class. Qed.
End Coefficients.
End RawFunctor.
End DPGroupCohomologyOrbitCoefficient.

Check DPGroupCohomologyOrbitCoefficient.centric_coefficient.
Check DPGroupCohomologyOrbitCoefficient.centric_coefficient_map.
Print Assumptions DPGroupCohomologyOrbitCoefficient.centric_coefficient.
Print Assumptions DPGroupCohomologyOrbitCoefficient.centric_coefficient_map.
