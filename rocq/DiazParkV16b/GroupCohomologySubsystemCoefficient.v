(** Native ordinary cohomology along an actual subsystem inclusion.  The
    subgroup charts and every naturality square are actual group maps. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso FusionMaps FusionSystems FusionOrbit FusionCentralizerMaps
  FusionSubsystemOrbit.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient LinkingCommaNaturality
  GroupCohomologyEmbeddingDiagramBase GroupCohomologyEmbeddingDiagramMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPLinkingCommaNaturality DPGroupCohomologyEmbeddingDiagramBase
  DPGroupCohomologyEmbeddingDiagramMaps.
Local Open Scope group_scope.

Module DPGroupCohomologySubsystemCoefficient.
Section Subsystem.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable C : {group S}.
Local Notation T := [the finGroupType of [subg C]%type].
Variable H : DPFusionSystem.system T.
Variable hH : forall (P Q : {group T}) (f : DPFusion.map P Q),
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (DPFusionSubgroup.lift f).
Local Notation incl := [morphism of @sgval S C].
Local Notation ambient_arrow := (@DPFusionSubsystem.ambient_arrow S F C H hH).

Lemma ambient_group_square (P Q : {group T}) (a : DPFusionSystem.arrow H P Q) :
  group_hom_comp (subgroup_image_hom incl P) (arrow_group_hom (ambient_arrow a)) =
    group_hom_comp (arrow_group_hom a) (subgroup_image_hom incl Q).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x; apply val_inj.
change (DPFusionSubgroup.lift (val a) (val (val x)) = val (val a (val x))).
exact: DPFusionSubgroup.liftE (valP x).
Qed.

Lemma ambient_group_image_map (P Q : {group T}) (a : DPFusionSystem.arrow H P Q) :
  subgroup_image_map (injm_sgval C) (arrow_group_hom a) =
    arrow_group_hom (ambient_arrow a).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => y.
pose x := subgroup_image_inverse (injm_sgval C) P y.
have hy : subgroup_image_hom incl P x = y := subgroup_image_inverse_hom (injm_sgval C) y.
rewrite -hy.
have ha := congr1 (fun f : {morphism [set: [subg P]] >->
    [subg (DPFusionSubgroup.ambient Q)]} => f x) (ambient_group_square a).
have hb := congr1 (fun f : {morphism [set: [subg P]] >->
    [subg (DPFusionSubgroup.ambient Q)]} => f x)
  (subgroup_image_map_square (injm_sgval C) (arrow_group_hom a)).
exact: eq_trans hb (esym ha).
Qed.

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation D := (DPGroupCohomologyOrbitCoefficient.coefficient H A n).
Local Notation E := (functor_comp (functor_op (@DPFusionSubsystem.orbit_functor S F C H hH))
  (DPGroupCohomologyOrbitCoefficient.coefficient F A n)).

Definition object_iso (P : {group T}) : @isomorphism (module_category R)
  (fobj D P) (fobj E P) := subgroup_image_cohomology_iso (injm_sgval C) A n P.

Lemma raw_naturality (P Q : {group T}) (a : DPFusionSystem.arrow H P Q) :
  module_hom_comp (DPGroupCohomologyOrbitCoefficient.raw_pull A n a)
    (iso_hom (object_iso P)) =
  module_hom_comp (iso_hom (object_iso Q))
    (DPGroupCohomologyOrbitCoefficient.raw_pull A n (ambient_arrow a)).
Proof.
change (module_hom_comp (pull A (arrow_group_hom a) n)
  (iso_hom (subgroup_image_cohomology_iso (injm_sgval C) A n P)) =
  module_hom_comp (iso_hom (subgroup_image_cohomology_iso (injm_sgval C) A n Q))
    (pull A (arrow_group_hom (ambient_arrow a)) n)).
rewrite -ambient_group_image_map; exact: subgroup_image_cohomology_naturality.
Qed.

Definition coefficient_nat_iso :
    @isomorphism (functor_category (opposite (DPFusionOrbit.orbit_category H))
      (module_category R)) D E.
Proof.
apply (@nat_iso_of_components _ _ D E object_iso).
move=> Q P a; move: a; apply: quotW => a.
change (module_hom_comp
  (DPGroupCohomologyOrbitCoefficient.orbit_pull A n (DPFusionOrbit.orbit_class a))
  (iso_hom (object_iso P)) =
  module_hom_comp (iso_hom (object_iso Q))
    (DPGroupCohomologyOrbitCoefficient.orbit_pull A n
      (DPFusionSubsystem.orbit_map hH (DPFusionOrbit.orbit_class a)))).
rewrite DPFusionSubsystem.orbit_map_class !DPGroupCohomologyOrbitCoefficient.orbit_pull_class.
exact: raw_naturality.
Defined.

Theorem coefficient_nat_iso_hom (P : {group T}) :
  component (iso_hom coefficient_nat_iso) P =
    pull A (subgroup_image_inverse (injm_sgval C) P) n.
Proof. reflexivity. Qed.

Theorem coefficient_nat_iso_inv (P : {group T}) :
  component (iso_inv coefficient_nat_iso) P =
    pull A (subgroup_image_hom incl P) n.
Proof. reflexivity. Qed.

End Subsystem.
End DPGroupCohomologySubsystemCoefficient.
