(** Actual subgroup-image maps and native cohomology naturality; no
    naturality or conjugation-compatibility law is supplied as an input. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  GroupCohomologyHomogeneousRestriction GroupCohomologyHomogeneousConjugation
  FiniteGroupFusionEmbeddingImage GroupCohomologyEmbeddingDiagramBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyHomogeneousRestriction DPGroupCohomologyHomogeneousConjugation
  DPFiniteGroupFusionEmbeddingImage DPGroupCohomologyEmbeddingDiagramBase.
Local Open Scope group_scope.

Module DPGroupCohomologyEmbeddingDiagramMaps.
Section Maps.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Variable injE : 'injm E.

Definition subgroup_image_map (P Q : {group N})
    (f : {morphism [set: [subg P]] >-> [subg Q]}) :=
  group_hom_comp (subgroup_image_inverse injE P)
    (group_hom_comp f (subgroup_image_hom E Q)).

Lemma subgroup_image_map_val (P Q : {group N})
    (f : {morphism [set: [subg P]] >-> [subg Q]}) (x : [subg (ambient E P)]) :
  val (subgroup_image_map f x) = E (val (f (subgroup_image_inverse injE P x))).
Proof. reflexivity. Qed.

Lemma subgroup_image_map_square (P Q : {group N})
    (f : {morphism [set: [subg P]] >-> [subg Q]}) :
  group_hom_comp (subgroup_image_hom E P) (subgroup_image_map f) =
    group_hom_comp f (subgroup_image_hom E Q).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x.
change (subgroup_image_hom E Q (f (subgroup_image_inverse injE P (subgroup_image_hom E P x))) =
  subgroup_image_hom E Q (f x)).
by rewrite subgroup_image_hom_inverse.
Qed.

Lemma subgroup_image_map_inverse_square (P Q : {group N})
    (f : {morphism [set: [subg P]] >-> [subg Q]}) :
  group_hom_comp (subgroup_image_map f) (subgroup_image_inverse injE Q) =
    group_hom_comp (subgroup_image_inverse injE P) f.
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x.
exact: subgroup_image_hom_inverse injE Q (f (subgroup_image_inverse injE P x)).
Qed.

Lemma subgroup_image_map_inclusion (P Q : {group N}) (hPQ : P \subset Q) :
  subgroup_image_map (subgroup_nested_hom hPQ) =
    subgroup_nested_hom (morphimS E hPQ).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x; apply val_inj.
rewrite subgroup_image_map_val !subgroup_nested_hom_val subgroup_image_inverse_val.
exact (ambient_inverseK injE (valP x)).
Qed.

Lemma image_conjugation_sub (P Q : {group N})
    (f : {morphism [set: [subg P]] >-> [subg Q]}) (g : G)
    (hf : forall x, E (val (f x)) = E (val x)^g) :
    ambient E P \subset (ambient E Q) :^ g^-1.
Proof.
apply/subsetP=> y /morphimP[x _ hx ->].
rewrite mem_conjg invgK -(hf (Sub x hx : [subg P])).
exact: ambient_mem (valP (f (Sub x hx : [subg P]))).
Qed.

Lemma subgroup_image_map_conjugation (P Q : {group N})
    (f : {morphism [set: [subg P]] >-> [subg Q]}) (g : G)
    (hf : forall x, E (val (f x)) = E (val x)^g) :
  subgroup_image_map f = @subgroup_conjugation_hom G (ambient E P) (ambient E Q)
    g^-1 (image_conjugation_sub hf).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x; apply val_inj.
rewrite subgroup_image_map_val subgroup_conjugation_hom_val invgK hf
  subgroup_image_inverse_val (ambient_inverseK injE (valP x)); reflexivity.
Qed.

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Theorem subgroup_image_cohomology_naturality (P Q : {group N})
    (f : {morphism [set: [subg P]] >-> [subg Q]}) :
  module_hom_comp (pull A f n) (iso_hom (subgroup_image_cohomology_iso injE A n P)) =
    module_hom_comp (iso_hom (subgroup_image_cohomology_iso injE A n Q))
      (pull A (subgroup_image_map f) n).
Proof.
rewrite !subgroup_image_cohomology_iso_hom -!pull_composition
  subgroup_image_map_inverse_square; reflexivity.
Qed.

Theorem subgroup_image_cohomology_restriction (P Q : {group N}) (hPQ : P \subset Q) :
  module_hom_comp (pull A (subgroup_nested_hom hPQ) n)
    (iso_hom (subgroup_image_cohomology_iso injE A n P)) =
  module_hom_comp (iso_hom (subgroup_image_cohomology_iso injE A n Q))
    (pull A (subgroup_nested_hom (morphimS E hPQ)) n).
Proof. rewrite -subgroup_image_map_inclusion; exact: subgroup_image_cohomology_naturality. Qed.

End Maps.
End DPGroupCohomologyEmbeddingDiagramMaps.
