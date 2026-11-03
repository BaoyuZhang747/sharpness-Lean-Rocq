From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology subtype_topology sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSubcomplex
  SimplicialBoundary TopologicalCategory TopologicalSimplexBasic TopologicalSimplexAffine
  TopologicalSimplexContinuity GeometricRealizationCarrier GeometricRealizationUniversal
  GeometricRealizationMaps GeometricRealizationStandardSimplex
  GeometricRealizationBoundaryAffine GeometricRealizationBoundaryFaces
  GeometricRealizationBoundarySupport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Module DPRealizationBoundaryEvaluation.
Import DPSimplexCategory DPSimplicialSet DPSimplicialSubcomplex
  DPTopological DPTopologicalSimplexAffine DPGeometricRealization
  DPGeometricRealizationUniversal DPGeometricRealizationMaps
  DPGeometricRealizationStandardSimplex DPRealizationBoundaryFaces DPRealizationBoundarySupport.

Section Evaluation.
Variable Real : realType.
Variable n : nat.
Let D := DPSimplicialBoundary.boundary_set n.
Let B := DPTopologicalSimplex.boundary_space Real n.

Definition boundary_evaluation_family : simplex_family Real D B :=
  fun k f t => exist _ (pushforward (proj1_sig f) t)
    (mem_set (@nonsurjective_pushforward_boundary Real k n (proj1_sig f) (proj2_sig f) t)).

Lemma boundary_evaluation_compatible : family_compatible boundary_evaluation_family.
Proof.
move=> k l a f t; apply: val_inj.
change (pushforward (ordinal_map_compose a (proj1_sig f)) t =
  pushforward (proj1_sig f) (pushforward a t)).
symmetry; exact: pushforward_composition.
Qed.

Lemma boundary_evaluation_family_continuous k (f : simplex D k) :
  continuous (@boundary_evaluation_family k f).
Proof.
apply: (@continuous_comp_initial _ _ _ set_val).
exact: DPTopologicalSimplexContinuity.pushforward_continuous.
Qed.

Definition boundary_evaluation : hom topological_category (realization_space Real D) B :=
  @descent_map Real D B boundary_evaluation_family boundary_evaluation_compatible
    boundary_evaluation_family_continuous.

Lemma boundary_evaluation_characteristic k (f : simplex D k) t :
  boundary_evaluation (@characteristic Real D k f t) = @boundary_evaluation_family k f t.
Proof. exact: (@descent_characteristic Real D B boundary_evaluation_family
  boundary_evaluation_compatible k f t). Qed.

Lemma boundary_evaluation_underlying z :
  set_val (boundary_evaluation z) =
  standard_evaluation Real n (realization_map Real (DPSimplicialBoundary.boundary_inclusion n) z).
Proof.
have [[[k f] t] <-] := realization_class_surjective z.
rewrite realization_map_characteristic standard_evaluation_characteristic.
rewrite boundary_evaluation_characteristic. reflexivity.
Qed.

Definition support_boundary_simplex (x : B) :
    simplex D (face_dimension (point_support (set_val x))) :=
  exist _ (support_inclusion (set_val x))
    (@support_inclusion_nonsurjective Real n (set_val x) (set_valP x)).

Definition boundary_normal_form (x : B) : realization Real D :=
  @characteristic Real D _ (support_boundary_simplex x) (support_point (set_val x)).

Lemma boundary_normal_form_evaluation x : boundary_evaluation (boundary_normal_form x) = x.
Proof.
rewrite /boundary_normal_form boundary_evaluation_characteristic.
apply: val_inj. exact: support_point_evaluation.
Qed.

Lemma boundary_evaluation_surjective x : exists z, boundary_evaluation z = x.
Proof. exists (boundary_normal_form x); exact: boundary_normal_form_evaluation. Qed.

End Evaluation.
End DPRealizationBoundaryEvaluation.
