(** Native group cohomology transport through an actual injective embedding,
    using literal subgroup image homomorphisms and their actual inverses. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  GroupCohomologyTransferCovarianceMaps FiniteGroupFusionEmbeddingImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyTransferCovarianceMaps DPFiniteGroupFusionEmbeddingImage.
Local Open Scope group_scope.

Module DPGroupCohomologyEmbeddingDiagramBase.
Section Embedding.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Variable injE : 'injm E.

Definition subgroup_image_hom (P : {group N}) := image_hom E (subsetT P).

Lemma subgroup_image_hom_val (P : {group N}) (x : [subg P]) :
  val (subgroup_image_hom P x) = E (val x).
Proof. reflexivity. Qed.

Definition subgroup_image_inverse (P : {group N}) :
    {morphism [set: [subg (ambient E P)]] >-> [subg P]}.
Proof.
apply: (Morphism (mfun := fun x : [subg (ambient E P)] =>
  (Sub (invm injE (val x)) (ambient_repr injE (valP x)) : [subg P]))).
move=> x y _ _; apply val_inj.
change (invm injE (val x * val y) = invm injE (val x) * invm injE (val y)).
exact: morphM (subsetP (ambient_sub E P) _ (valP x))
  (subsetP (ambient_sub E P) _ (valP y)).
Defined.

Lemma subgroup_image_inverse_val (P : {group N}) (x : [subg (ambient E P)]) :
  val (subgroup_image_inverse P x) = invm injE (val x).
Proof. reflexivity. Qed.

Lemma subgroup_image_hom_inverse (P : {group N}) :
  cancel (subgroup_image_hom P) (subgroup_image_inverse P).
Proof.
move=> x; apply val_inj.
by rewrite subgroup_image_inverse_val subgroup_image_hom_val invmE ?inE.
Qed.

Lemma subgroup_image_inverse_hom (P : {group N}) :
  cancel (subgroup_image_inverse P) (subgroup_image_hom P).
Proof.
move=> x; apply val_inj.
rewrite subgroup_image_hom_val subgroup_image_inverse_val.
exact (ambient_inverseK injE (valP x)).
Qed.

Lemma subgroup_image_hom_inverse_eq (P : {group N}) :
  group_hom_comp (subgroup_image_hom P) (subgroup_image_inverse P) =
    group_hom_identity [the finGroupType of [subg P]%type].
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext.
exact: subgroup_image_hom_inverse.
Qed.

Lemma subgroup_image_inverse_hom_eq (P : {group N}) :
  group_hom_comp (subgroup_image_inverse P) (subgroup_image_hom P) =
    group_hom_identity [the finGroupType of [subg (ambient E P)]%type].
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext.
exact: subgroup_image_inverse_hom.
Qed.

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Definition subgroup_image_cohomology_iso (P : {group N}) :
    @isomorphism (module_category R)
      (value R [the finGroupType of [subg P]%type] A n)
      (value R [the finGroupType of [subg (ambient E P)]%type] A n).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (pull A (subgroup_image_inverse P) n) (pull A (subgroup_image_hom P) n) _ _).
- change (module_hom_comp (pull A (subgroup_image_inverse P) n)
    (pull A (subgroup_image_hom P) n) = module_hom_id _).
  by rewrite -pull_composition subgroup_image_hom_inverse_eq pull_identity.
- change (module_hom_comp (pull A (subgroup_image_hom P) n)
    (pull A (subgroup_image_inverse P) n) = module_hom_id _).
  by rewrite -pull_composition subgroup_image_inverse_hom_eq pull_identity.
Defined.

Theorem subgroup_image_cohomology_iso_hom (P : {group N}) :
  iso_hom (subgroup_image_cohomology_iso P) = pull A (subgroup_image_inverse P) n.
Proof. reflexivity. Qed.

Theorem subgroup_image_cohomology_iso_inv (P : {group N}) :
  iso_inv (subgroup_image_cohomology_iso P) = pull A (subgroup_image_hom P) n.
Proof. reflexivity. Qed.

End Embedding.
End DPGroupCohomologyEmbeddingDiagramBase.
