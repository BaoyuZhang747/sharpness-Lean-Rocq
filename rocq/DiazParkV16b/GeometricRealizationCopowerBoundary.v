(** Closed boundary attachments and T1 cell families for actual realized copowers. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology
  normedtype matrix_normedtype subtype_topology sigT_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialBoundary SimplicialCopower
  TopologicalCategory TopologicalSimplexBasic TopologicalCoproductHomotopy
  TopologicalCoproductHomeomorphism TopologicalHomeomorphismTransport TopologicalPushoutOverlap
  SingularSimplexRadialFamily SingularSimplexRadialComplement
  GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationStandardSimplex
  GeometricRealizationBoundaryHomeomorphism GeometricRealizationBoundaryTopology
  GeometricRealizationCopower GeometricRealizationCopowerNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldNormedType.Exports DPTopological DPTopologicalCoproductHomotopy
  DPTopologicalCoproductHomeomorphism DPTopologicalHomeomorphismTransport DPTopologicalPushoutOverlap
  DPSimplicialSet DPSimplicialCopower DPSingularSimplexRadialFamily DPSingularSimplexRadialComplement
  DPGeometricRealization DPGeometricRealizationMaps DPGeometricRealizationStandardSimplex
  DPRealizationBoundaryHomeomorphism DPRealizationBoundaryTopology
  DPGeometricRealizationCopower DPGeometricRealizationCopowerNaturality.
Local Open Scope classical_set_scope.

Module DPGeometricRealizationCopowerBoundary.
Section Boundary.
Variable Real : realType.
Variable I : Type.
Variable n : nat.
Let IC := [the choiceType of {classic I}].

Definition realized_cells_coordinates : homeomorphism
    (realization_space Real (copower I (standard_simplex n)))
    (@cell_family Real IC (fun _ => n)) :=
  homeomorphism_compose (realization_copower_homeomorphism Real I (standard_simplex n))
    (@family_homeomorphism IC (fun _ => realization_space Real (standard_simplex n))
      (fun _ => DPTopologicalSimplex.simplex_space Real n)
      (fun _ => realized_standard_simplex_homeomorphism Real n)).

Definition realized_boundaries_coordinates : homeomorphism
    (realization_space Real (copower I (DPSimplicialBoundary.boundary_set n)))
    (@boundary_family Real IC (fun _ => n)) :=
  homeomorphism_compose (realization_copower_homeomorphism Real I (DPSimplicialBoundary.boundary_set n))
    (@family_homeomorphism IC (fun _ => realization_space Real (DPSimplicialBoundary.boundary_set n))
      (fun _ => DPTopologicalSimplex.boundary_space Real n)
      (fun _ => realized_boundary_homeomorphism Real n)).

Let boundary_map := realization_map Real (@copower_map I _ _ (DPSimplicialBoundary.boundary_inclusion n)).

Lemma realized_boundary_copower_square z :
  iso_hom realized_cells_coordinates (boundary_map z) =
    family_boundary_inclusion Real (fun _ : IC => n) (iso_hom realized_boundaries_coordinates z).
Proof.
change (@family_map IC _ _ (fun _ => standard_evaluation Real n)
  (copower_forward Real I (standard_simplex n) (boundary_map z)) =
  family_boundary_inclusion Real (fun _ : IC => n)
    (@family_map IC _ _ (fun _ => iso_hom (realized_boundary_homeomorphism Real n))
      (copower_forward Real I (DPSimplicialBoundary.boundary_set n) z))).
rewrite realization_copower_natural_at.
case: (copower_forward Real I (DPSimplicialBoundary.boundary_set n) z) => a x.
change (existT (fun _ : IC => DPTopologicalSimplex.simplex_space Real n) a
  (standard_evaluation Real n (realization_map Real (DPSimplicialBoundary.boundary_inclusion n) x)) =
  existT (fun _ : IC => DPTopologicalSimplex.simplex_space Real n) a
    (val (iso_hom (realized_boundary_homeomorphism Real n) x))).
congr (existT _ a _).
exact (congr1 (fun f : hom topological_category
  (realization_space Real (DPSimplicialBoundary.boundary_set n)) (DPTopologicalSimplex.simplex_space Real n) => f x)
  (realized_boundary_inclusion_compatibility Real n)).
Qed.

Theorem realized_boundary_copower_injective : injective boundary_map.
Proof.
exact: (@homeomorphic_map_injective _ _ _ _ realized_boundaries_coordinates realized_cells_coordinates
  boundary_map (family_boundary_inclusion Real (fun _ : IC => n))
  realized_boundary_copower_square (@boundary_family_inclusion_injective Real IC (fun _ => n))).
Qed.

Theorem realized_boundary_copower_closed (S : set (realization_space Real (copower I (DPSimplicialBoundary.boundary_set n))))
    (hS : closed S) : closed (boundary_map @` S).
Proof.
exact: (@homeomorphic_map_closed _ _ _ _ realized_boundaries_coordinates realized_cells_coordinates
  boundary_map (family_boundary_inclusion Real (fun _ : IC => n)) realized_boundary_copower_square
  (@boundary_family_inclusion_closed Real IC (fun _ => n)) S hS).
Qed.

Theorem realized_cell_copower_accessible : accessible_space (realization_space Real (copower I (standard_simplex n))).
Proof.
apply: (homeomorphism_accessible realized_cells_coordinates).
apply: family_accessible => a; apply: hausdorff_accessible.
apply: subtype_hausdorff; exact: norm_hausdorff.
Qed.

End Boundary.
End DPGeometricRealizationCopowerBoundary.
