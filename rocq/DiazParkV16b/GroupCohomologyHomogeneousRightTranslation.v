(** Right translation is an actual equivariant resolution endomorphism lifting
    the identity, hence induces the identity on invariant Hom cohomology. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryDiagramHom
  CategoryDiagramHomLimit CategoryEnoughProjectivesResolution
  CategoryEnoughProjectivesComparison ProjectiveExtComplex
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  BarFreeModule MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousPaths
  GroupCohomologyHomogeneousMaps GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousProjective
  GroupCohomologyHomogeneousResolution GroupCohomologyHomogeneousCohomology
  GroupCohomologyResolutionComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DiazParkFreeModule DPEnoughProjectiveResolutions
  DPProjectiveComparison DPProjectiveExt DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DPGroupCohomologyHomogeneousPaths
  DPGroupCohomologyHomogeneousMaps DPGroupCohomologyHomogeneousComplex
  DPGroupCohomologyHomogeneousEquivariance DPGroupCohomologyHomogeneousProjective
  DPGroupCohomologyHomogeneousResolution DPGroupCohomologyHomogeneousCohomology
  DPGroupCohomologyResolutionComparison.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousRightTranslation.

Lemma right_vertices_left (G : finGroupType) (a x : G) n (v : power G n) :
  vertices_map (fun t => (t*x)%g) n (left_translate n a v) =
    left_translate n a (vertices_map (fun t => (t*x)%g) n v).
Proof.
elim: n v => [|n IH] v; first reflexivity.
by case: v => t v; rewrite /= mulgA IH.
Qed.

Lemma right_map_left (R : pzRingType) (G : finGroupType) (a x : G) n
    (v : homogeneous_term R G n) :
  homogeneous_map R (fun t => (t*x)%g) n (homogeneous_action R n a v) =
  homogeneous_action R n a (homogeneous_map R (fun t => (t*x)%g) n v).
Proof.
rewrite /homogeneous_map /homogeneous_action -!free_map_composition.
congr (free_map R _ v); apply functional_extensionality_dep => t.
exact: right_vertices_left.
Qed.

Section RightTranslation.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable H : {group G}.
Variable x : G.
Local Notation HS := [the finGroupType of [subg H]].
Local Notation C := (opposite (group_category HS)).
Local Notation B := (constant_regular_diagram R C).
Local Notation E := (homogeneous_resolution R H).

Definition right_translation_term n : nat_trans (homogeneous_diagram R H n)
    (homogeneous_diagram R H n).
Proof.
refine (@Build_nat_trans C (module_category R) (homogeneous_diagram R H n) (homogeneous_diagram R H n)
  (fun _ => module_hom_of_linear (homogeneous_map R (fun t => (t*x)%g) n)) _).
move=> a b h; apply module_hom_ext => v; exact: right_map_left.
Defined.

Definition right_translation_resolution : projective_resolution_map E E (nat_id B).
Proof.
refine (@Build_projective_resolution_map R C B B E E (nat_id B)
  right_translation_term _ _).
- move=> n a v; exact: homogeneous_map_boundary.
- apply nat_trans_ext => a; apply module_hom_ext => v.
  exact: homogeneous_map_augmentation.
Defined.

Definition homogeneous_identity_resolution : projective_resolution_map E E (nat_id B).
Proof.
refine (@Build_projective_resolution_map R C B B E E (nat_id B)
  (fun n => nat_id (projective_term E n)) _ _).
- move=> n a v; reflexivity.
- apply nat_trans_ext => a; apply module_hom_ext => v; reflexivity.
Defined.

Variable A : lmodType R.

Definition ambient_right_translation :
    cochain_map (@ambient_hom_complex R G H A) (@ambient_hom_complex R G H A) :=
  projective_hom_map (trivial_codiagram R HS A) right_translation_resolution.

Lemma ambient_right_translation_component n
    (f : cochain_term (@ambient_hom_complex R G H A) n) a v :
  module_hom_fun (component (cochain_map_at ambient_right_translation n f) a) v =
  module_hom_fun (component f a) (homogeneous_map R (fun t => (t*x)%g) n v).
Proof. reflexivity. Qed.

Theorem ambient_right_translation_cohomology_identity n
    (q : cohomology (@ambient_hom_complex R G H A) n) :
  cohomology_map ambient_right_translation n q = q.
Proof.
have he := congr1 (fun k => module_hom_fun k q)
  (@specified_comparison_independent R C B (trivial_codiagram R HS A) E E
    right_translation_resolution homogeneous_identity_resolution n).
change (cohomology_map ambient_right_translation n q =
  cohomology_map (projective_hom_map (trivial_codiagram R HS A)
    homogeneous_identity_resolution) n q) in he.
rewrite he.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; apply diagram_hom_ext => a v; reflexivity.
Qed.

End RightTranslation.
End DPGroupCohomologyHomogeneousRightTranslation.


