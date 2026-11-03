(** The shared homogeneous resolution computes the displayed native group
    cohomology, with a literal normalized comparison on cochains. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHomLimit
  CategoryDiagramExt CategoryEnoughProjectivesResolution CategoryComplexIso
  HomologicalComplex HomologicalMaps HomologicalCohomology HomologicalCohomologyMaps
  HomologicalModuleIso BarPaths BarFreeModule BarResolutionHom ProjectiveExtComplex
  ProjectiveExtBar MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousPaths
  GroupCohomologyHomogeneousMaps GroupCohomologyHomogeneousResolution
  GroupCohomologyHomogeneousComparison GroupCohomologyResolutionComparison.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPEnoughProjectiveResolutions DPProjectiveExt DPProjectiveExtBar
  DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkBarPaths DiazParkFreeModule DiazParkBarResolutionHom
  DPGroupCohomologyHomogeneousPaths DPGroupCohomologyHomogeneousMaps
  DPGroupCohomologyHomogeneousResolution DPGroupCohomologyHomogeneousComparison
  DPGroupCohomologyResolutionComparison.

Module DPGroupCohomologyHomogeneousCohomology.
Section Computation.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable H : {group G}.
Variable A : lmodType R.
Local Notation HS := [the finGroupType of [subg H]].
Local Notation C := (opposite (group_category HS)).
Local Notation D := (trivial_codiagram R HS A).

Definition ambient_hom_complex : @cochain_complex R :=
  projective_hom_complex (homogeneous_resolution R H) D.

Definition ambient_to_native_cochain : cochain_map ambient_hom_complex (complex R HS A) :=
  cochain_composition (projective_hom_map D (native_to_ambient_resolution R H))
    (term_iso_cochain_map (@bar_hom_term_commutes R (group_category HS) D)).

Definition ambient_native_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology ambient_hom_complex n] (value R HS A n) :=
  module_iso_comp
    (@specified_comparison_iso R C (constant_regular_diagram R C) D
      (@bar_projective_resolution R (group_category HS)) (homogeneous_resolution R H)
      (native_to_ambient_resolution R H) n)
    (bar_projective_cohomology_iso D n).

Lemma ambient_native_iso_hom n :
  iso_hom (ambient_native_iso n) =
    module_hom_of_linear (cohomology_map ambient_to_native_cochain n).
Proof.
apply module_hom_ext => q.
change (cohomology_map
    (term_iso_cochain_map (@bar_hom_term_commutes R (group_category HS) D)) n
    (cohomology_map (projective_hom_map D (native_to_ambient_resolution R H)) n q) =
  cohomology_map (cochain_composition
    (projective_hom_map D (native_to_ambient_resolution R H))
    (term_iso_cochain_map (@bar_hom_term_commutes R (group_category HS) D))) n q).
symmetry; exact: cohomology_map_composition.
Qed.

(** Native inhomogeneous bar cochains are obtained by evaluation on
    (1, h1, h1*h2, ..., h1*...*hn), embedded in the ambient group. *)
Lemma ambient_to_native_cochain_at n (f : cochain_term ambient_hom_complex n)
    (p : @path_from (group_category HS) n tt) :
  cochain_map_at ambient_to_native_cochain n f tt p =
    module_hom_fun (component f tt)
      (free_basis R (vertices_map (subgroup_inclusion_hom H) n.+1
        (@resolution_generator_to_homogeneous HS n tt
          (existT _ tt (1%g, p))))).
Proof.
change (module_hom_fun (component f tt)
    (native_to_ambient_component R H n (free_basis R (existT _ tt (1%g, p)))) =
  module_hom_fun (component f tt)
    (free_basis R (vertices_map (subgroup_inclusion_hom H) n.+1
      (@resolution_generator_to_homogeneous HS n tt (existT _ tt (1%g, p)))))).
by rewrite native_to_ambient_basis.
Qed.

Definition ambient_ext_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology ambient_hom_complex n]
    (diagram_ext R (constant_regular_diagram R C) D n) :=
  module_iso_comp (ambient_native_iso n) (ext_iso R HS A n).

End Computation.
End DPGroupCohomologyHomogeneousCohomology.
