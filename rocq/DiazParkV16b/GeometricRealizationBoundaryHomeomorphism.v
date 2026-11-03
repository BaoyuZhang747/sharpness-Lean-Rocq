From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology subtype_topology sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialBoundary TopologicalCategory TopologicalSimplexBasic
  GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationStandardSimplex
  GeometricRealizationBoundaryEvaluation GeometricRealizationBoundaryNormalization
  GeometricRealizationBoundaryCompact GeometricRealizationBoundaryTopology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPRealizationBoundaryHomeomorphism.
Import DPTopological DPGeometricRealization DPGeometricRealizationMaps
  DPGeometricRealizationStandardSimplex DPRealizationBoundaryEvaluation
  DPRealizationBoundaryNormalization DPRealizationBoundaryCompact DPRealizationBoundaryTopology.

Section Homeomorphism.
Variable Real : realType.
Variable n : nat.
Let D := DPSimplicialBoundary.boundary_set n.
Let B := DPTopologicalSimplex.boundary_space Real n.

Lemma boundary_normal_form_continuous : continuous (@boundary_normal_form Real n).
Proof.
apply: (@compact_inverse_continuous (realization_space Real D) B
  (boundary_evaluation Real n) (@boundary_normal_form Real n)).
- exact: cts_fun.
- exact: realized_boundary_compact.
- exact: coordinate_boundary_hausdorff.
- exact: boundary_evaluation_normal_form.
- exact: boundary_normal_form_evaluation.
Qed.

Definition realized_boundary_homeomorphism : homeomorphism (realization_space Real D) B.
Proof.
apply: (@homeomorphism_of_inverse (realization_space Real D) B
  (boundary_evaluation Real n) (@boundary_normal_form Real n)).
- exact: cts_fun.
- exact: boundary_normal_form_continuous.
- exact: boundary_evaluation_normal_form.
- exact: boundary_normal_form_evaluation.
Defined.

Lemma realized_boundary_homeomorphism_forward z :
  iso_hom realized_boundary_homeomorphism z = boundary_evaluation Real n z.
Proof. reflexivity. Qed.

Lemma realized_boundary_homeomorphism_inverse x :
  iso_inv realized_boundary_homeomorphism x = boundary_normal_form x.
Proof. reflexivity. Qed.

Definition coordinate_boundary_inclusion :
    hom topological_category B (DPTopologicalSimplex.simplex_space Real n).
Proof.
apply: (@continuous_map B (DPTopologicalSimplex.simplex_space Real n) set_val).
exact: initial_continuous.
Defined.

Theorem realized_boundary_inclusion_compatibility :
  compose (realization_map Real (DPSimplicialBoundary.boundary_inclusion n))
    (standard_evaluation Real n) =
  compose (iso_hom realized_boundary_homeomorphism) coordinate_boundary_inclusion.
Proof.
apply: topological_hom_ext => z. symmetry. exact: boundary_evaluation_underlying.
Qed.

End Homeomorphism.

Lemma realized_boundary_zero_empty (Real : realType)
    (z : realization Real (DPSimplicialBoundary.boundary_set 0)) : False.
Proof.
have [[[k f] t] _] := realization_class_surjective z.
exact: (DPSimplicialBoundary.boundary_zero_empty f).
Qed.

End DPRealizationBoundaryHomeomorphism.
