(** Native cohomology transported along the genuine image orbit equivalence.
    Every component and every raw-arrow square uses the actual subgroup chart. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import GroupCohomologyFunctor GroupCohomologyPullback
  GroupCohomologyOrbitCoefficient LinkingCommaNaturality
  GroupCohomologyEmbeddingDiagramBase GroupCohomologyEmbeddingDiagramMaps
  FiniteGroupFusion FiniteGroupFusionEmbedding FiniteGroupFusionEmbeddingImage
  FiniteGroupFusionEmbeddingOrbitRaw FiniteGroupFusionEmbeddingOrbitClasses
  FiniteGroupFusionEmbeddingOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyFunctor DPGroupCohomologyPullback DPLinkingCommaNaturality
  DPGroupCohomologyEmbeddingDiagramBase DPGroupCohomologyEmbeddingDiagramMaps
  DPFiniteGroupFusionEmbeddingImage DPFiniteGroupFusionEmbeddingOrbit
  DPFiniteGroupFusionEmbeddingOrbitClasses
  DPFiniteGroupFusionEmbeddingOrbitEquivalence.
Local Open Scope group_scope.

Module DPGroupCohomologyEmbeddingOrbitCoefficient.
Section Coefficient.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Variable injE : 'injm E.
Local Notation T := [the finGroupType of [subg (image_group E)]%type].
Local Notation e := (image_equivalence E).
Local Notation F := (DPFiniteGroupFusionEmbedding.system E).
Local Notation H := (DPFiniteGroupFusion.system (image_group E)).

Lemma image_equivalence_injm : 'injm e.
Proof. apply/injmP=> x y _ _; exact: (can_inj (image_equivalence_inverse injE)). Qed.

Lemma forward_group_square (P Q : {group N}) (a : DPFusionSystem.arrow F P Q) :
  group_hom_comp (subgroup_image_hom e P) (arrow_group_hom (forward_arrow injE a)) =
    group_hom_comp (arrow_group_hom a) (subgroup_image_hom e Q).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x; apply val_inj.
exact (@forward_rawE N G E injE P Q (val a) (val x) (valP x)).
Qed.

Lemma forward_group_image_map (P Q : {group N}) (a : DPFusionSystem.arrow F P Q) :
  subgroup_image_map image_equivalence_injm (arrow_group_hom a) =
    arrow_group_hom (forward_arrow injE a).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => y.
pose x := subgroup_image_inverse image_equivalence_injm P y.
have hy : subgroup_image_hom e P x = y := subgroup_image_inverse_hom image_equivalence_injm y.
rewrite -hy.
have ha := congr1 (fun f : {morphism [set: [subg P]] >->
    [subg (forward_subgroup E Q)]} => f x) (forward_group_square a).
have hb := congr1 (fun f : {morphism [set: [subg P]] >->
    [subg (forward_subgroup E Q)]} => f x)
  (subgroup_image_map_square image_equivalence_injm (arrow_group_hom a)).
exact: eq_trans hb (esym ha).
Qed.

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation D := (DPGroupCohomologyOrbitCoefficient.coefficient F A n).
Local Notation I := (functor_comp (functor_op (orbit_functor injE))
  (DPGroupCohomologyOrbitCoefficient.coefficient H A n)).

Definition object_iso (P : {group N}) : @isomorphism (module_category R)
  (fobj D P) (fobj I P) := subgroup_image_cohomology_iso image_equivalence_injm A n P.

Lemma raw_naturality (P Q : {group N}) (a : DPFusionSystem.arrow F P Q) :
  module_hom_comp (DPGroupCohomologyOrbitCoefficient.raw_pull A n a) (iso_hom (object_iso P)) =
  module_hom_comp (iso_hom (object_iso Q))
    (DPGroupCohomologyOrbitCoefficient.raw_pull A n (forward_arrow injE a)).
Proof.
change (module_hom_comp (pull A (arrow_group_hom a) n)
  (iso_hom (subgroup_image_cohomology_iso image_equivalence_injm A n P)) =
  module_hom_comp (iso_hom (subgroup_image_cohomology_iso image_equivalence_injm A n Q))
    (pull A (arrow_group_hom (forward_arrow injE a)) n)).
rewrite -forward_group_image_map; exact: subgroup_image_cohomology_naturality.
Qed.

Definition coefficient_nat_iso :
    @isomorphism (functor_category (opposite (DPFusionOrbit.orbit_category F))
      (module_category R)) D I.
Proof.
apply (@nat_iso_of_components _ _ D I object_iso).
move=> Q P a; move: a; apply: quotW => a.
change (module_hom_comp
  (DPGroupCohomologyOrbitCoefficient.orbit_pull A n (DPFusionOrbit.orbit_class a))
    (iso_hom (object_iso P)) =
  module_hom_comp (iso_hom (object_iso Q))
    (DPGroupCohomologyOrbitCoefficient.orbit_pull A n
      (fmap (orbit_functor injE) (DPFusionOrbit.orbit_class a)))).
rewrite orbit_functor_class !DPGroupCohomologyOrbitCoefficient.orbit_pull_class.
exact: raw_naturality.
Defined.

Definition centric_coefficient_nat_iso :
    @isomorphism (functor_category (opposite (DPFusionOrbit.centric_orbit_category F))
      (module_category R))
      (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)
      (functor_comp (functor_op (centric_orbit_functor injE))
        (DPGroupCohomologyOrbitCoefficient.centric_coefficient H A n)).
Proof.
apply (@nat_iso_of_components (opposite (DPFusionOrbit.centric_orbit_category F))
  (module_category R)
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)
  (functor_comp (functor_op (centric_orbit_functor injE))
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient H A n))
  (fun P : DPFusionOrbit.centric_object F => object_iso (val P))).
move=> Q P a; exact (naturality (iso_hom coefficient_nat_iso) a).
Defined.

Theorem centric_coefficient_nat_iso_hom (P : DPFusionOrbit.centric_object F) :
  component (iso_hom centric_coefficient_nat_iso) P =
    pull A (subgroup_image_inverse image_equivalence_injm (val P)) n.
Proof. reflexivity. Qed.

Theorem centric_coefficient_nat_iso_inv (P : DPFusionOrbit.centric_object F) :
  component (iso_inv centric_coefficient_nat_iso) P =
    pull A (subgroup_image_hom e (val P)) n.
Proof. reflexivity. Qed.
End Coefficient.
End DPGroupCohomologyEmbeddingOrbitCoefficient.
