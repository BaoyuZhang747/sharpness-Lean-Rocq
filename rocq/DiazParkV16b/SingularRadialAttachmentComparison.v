(** Relative excision for the actual attachment of an arbitrary family of simplex cells. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy TopologicalSimplexBasic
  TopologicalPushoutCarrier TopologicalPushoutUniversal TopologicalPushoutEmbedding TopologicalCoproductSubspaces
  SingularSimplexRadialContinuity SingularSimplexRadialFamily SingularSimplexRadialNeighborhoodMaps
  SingularSimplexRadialNeighborhood SingularSimplexRadialNeighborhoodDeformation SingularSimplexRadialComplement
  SingularCohomology SingularChainMapsLaws SingularChainComparison SingularRelativePairs
  SingularRelativeCovers SingularRelativeNeighborhoods SingularChainExcisionSubspaces
  ChainComplex ChainMapImage ChainQuasiIsomorphism ChainQuasiIsomorphismLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPTopologicalSimplex DPTopologicalPushoutCarrier
  DPTopologicalPushoutUniversal DPTopologicalPushoutEmbedding DPTopologicalCoproductSubspaces
  DPSingularSimplexRadialContinuity DPSingularSimplexRadialFamily DPSingularSimplexRadialNeighborhoodMaps
  DPSingularSimplexRadialNeighborhood DPSingularSimplexRadialNeighborhoodDeformation DPSingularSimplexRadialComplement
  DPSingularCohomology DPSingularChainMapsLaws DPSingularChainComparison DPSingularRelativePairs
  DPSingularRelativeCovers DPSingularRelativeNeighborhoods DPSingularChainExcisionSubspaces
  DPChainComplex DPChainMapImage DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws.
Local Open Scope classical_set_scope.
Module DPSingularRadialAttachmentComparison.
Section Attachment.
Variable Real : realType.
Variable R : pzRingType.
Variable I : choiceType.
Variable d : I -> nat.
Variable X : topologicalType.
Variable j : continuousType (boundary_family Real d) X.

Definition radial_punctured_subspace_homeomorphism : homeomorphism
    (punctured_family Real d) (subset_space (@family_punctured_set Real I d)) :=
  @family_subspaces_homeomorphism I (fun i => simplex_space Real (d i))
    (fun i => @punctured_set Real (d i)).

Definition radial_boundary_to_neighborhood : continuousType (boundary_family Real d)
    (subset_space (@family_punctured_set Real I d)) :=
  continuous_compose (family_boundary_punctured Real d) (iso_hom radial_punctured_subspace_homeomorphism).

Lemma radial_boundary_to_neighborhood_val z :
  val (radial_boundary_to_neighborhood z) = family_boundary_inclusion Real d z.
Proof. by case: z => i z. Qed.

Lemma radial_family_retraction z :
  family_radial_projection Real d (family_boundary_punctured Real d z) = z.
Proof.
exact (congr1 (fun f : continuousType (boundary_family Real d) (boundary_family Real d) => f z)
  (@family_radial_retraction Real I d)).
Qed.

Lemma radial_boundary_to_neighborhood_quasi_isomorphism :
  quasi_isomorphism (singular_chain_map Real R radial_boundary_to_neighborhood).
Proof.
apply: (@quasi_isomorphism_ext R _ _
  (chain_composition (singular_chain_map Real R (family_boundary_punctured Real d))
    (singular_chain_map Real R (iso_hom radial_punctured_subspace_homeomorphism)))).
- move=> n z; symmetry; exact: singular_chain_composition.
- apply: quasi_isomorphism_composition.
  + exact (@deformation_retraction_quasi_isomorphism Real R _ _
      (family_boundary_punctured Real d) (family_radial_projection Real d)
      radial_family_retraction (family_radial_homotopy Real d)).
  + exact (@singular_homeomorphism_quasi_isomorphism Real R _ _ radial_punctured_subspace_homeomorphism).
Qed.

Lemma radial_old_neighborhood_quasi_isomorphism :
  quasi_isomorphism (singular_chain_map Real R (radial_old_to_neighborhood j)).
Proof.
exact (@deformation_retraction_quasi_isomorphism Real R _ _
  (radial_old_to_neighborhood j) (radial_neighborhood_retraction j)
  (@radial_neighborhood_retraction_equation Real I d X j) (radial_neighborhood_deformation j)).
Qed.

Lemma radial_attachment_square z :
  attaching_left_map (family_boundary_inclusion Real d) j (family_boundary_inclusion Real d z) =
    attaching_right_map (family_boundary_inclusion Real d) j (j z).
Proof.
exact (congr1 (fun f : continuousType (boundary_family Real d) (@full_radial_attachment Real I d X j) => f z)
  (attaching_commutes (family_boundary_inclusion Real d) j)).
Qed.

Definition radial_attachment_relative_map := @singular_relative_map Real R
  (boundary_family Real d) (cell_family Real d) X (@full_radial_attachment Real I d X j)
  (family_boundary_inclusion Real d) (attaching_right_map (family_boundary_inclusion Real d) j)
  j (attaching_left_map (family_boundary_inclusion Real d) j) radial_attachment_square.

Lemma radial_neighborhood_forward b : @family_punctured_set Real I d b ->
  @radial_neighborhood Real I d X j (attaching_left_map (family_boundary_inclusion Real d) j b).
Proof. exact: (proj1 (radial_overlap_correspondence j b)). Qed.

Theorem radial_attachment_relative_quasi_isomorphism : quasi_isomorphism radial_attachment_relative_map.
Proof.
apply: (@relative_attachment_quasi_isomorphism Real R
  (boundary_family Real d) (cell_family Real d) X (@full_radial_attachment Real I d X j)
  (family_boundary_inclusion Real d) (attaching_right_map (family_boundary_inclusion Real d) j)
  j (attaching_left_map (family_boundary_inclusion Real d) j) radial_attachment_square
  (@family_punctured_set Real I d) (@radial_neighborhood Real I d X j) radial_neighborhood_forward
  radial_boundary_to_neighborhood (radial_old_to_neighborhood j)
  radial_boundary_to_neighborhood_val (@radial_old_to_neighborhood_val Real I d X j)).
- exact: boundary_family_inclusion_injective.
- exact (pushout_right_injective (attaching_pushout (family_boundary_inclusion Real d) j)
    (@boundary_family_inclusion_injective Real I d)).
- exact: radial_boundary_to_neighborhood_quasi_isomorphism.
- exact: radial_old_neighborhood_quasi_isomorphism.
- apply: (@cover_relative_quasi_isomorphism Real R _ _
    (attaching_left_map (family_boundary_inclusion Real d) j)
    (@family_punctured_set Real I d) (@radial_cell_complement Real I d)
    (@radial_neighborhood Real I d X j) (@radial_attachment_complement Real I d X j)
    radial_neighborhood_forward (radial_complement_homeomorphism j) (radial_overlap_homeomorphism j)
    (@radial_complement_homeomorphism_val Real I d X j) (@radial_overlap_homeomorphism_val Real I d X j)).
  + exact: radial_cell_complement_open.
  + exact: family_punctured_set_open.
  + exact: radial_attachment_complement_open.
  + exact: radial_neighborhood_open.
  + move=> b; case: (@radial_cell_cover Real I d b) => h; [by right | by left].
  + move=> y; case: (@radial_attachment_cover Real I d X j y) => h; [by right | by left].
Qed.
End Attachment.
End DPSingularRadialAttachmentComparison.
