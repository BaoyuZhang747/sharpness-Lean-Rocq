From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology subtype_topology sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSubcomplex
  SimplicialBoundary TopologicalCategory TopologicalSimplexBasic TopologicalSimplexCompact
  GeometricRealizationCarrier GeometricRealizationBoundaryFaces
  GeometricRealizationBoundarySupport GeometricRealizationBoundaryEvaluation
  GeometricRealizationBoundaryNormalization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Module DPRealizationBoundaryCompact.
Import DPSimplexCategory DPSimplicialSet DPSimplicialSubcomplex DPGeometricRealization
  DPRealizationBoundaryFaces DPRealizationBoundarySupport DPRealizationBoundaryEvaluation
  DPRealizationBoundaryNormalization.

Section Compactness.
Variable Real : realType.
Variable n : nat.
Let D := DPSimplicialBoundary.boundary_set n.

Definition proper_face :=
  {A : {set 'I_n.+1} | (0 < #|A|)%N && (A != finset.setT)}.
Definition proper_face_finType := [the finType of proper_face].

Lemma proper_face_positive (A : proper_face) : (0 < #|val A|)%N.
Proof. exact (proj1 (andP (valP A))). Qed.

Lemma proper_face_proper (A : proper_face) : val A != finset.setT.
Proof. exact (proj2 (andP (valP A))). Qed.

Definition proper_face_simplex (A : proper_face) : simplex D (face_dimension (val A)) :=
  exist _ (@face_inclusion n (val A) (proper_face_positive A))
    (@face_inclusion_nonsurjective n (val A) (proper_face_positive A) (proper_face_proper A)).

Definition proper_face_image (A : proper_face) : set (realization_space Real D) :=
  (@characteristic Real D _ (proper_face_simplex A)) @` setT.

Lemma proper_face_image_compact A : compact (proper_face_image A).
Proof.
apply: continuous_compact.
- apply: continuous_subspaceT. exact: characteristic_continuous.
- exact: DPTopologicalSimplexCompact.simplex_compact.
Qed.

Lemma realized_boundary_finite_face_cover :
  @setT (realization_space Real D) =
    \big[setU/set0]_(A : proper_face_finType) proper_face_image A.
Proof.
rewrite -(bigcup_pred predT proper_face_image).
apply/seteqP; split=> z hz; last exact I.
pose x := boundary_evaluation Real n z.
have hp : (0 < #|point_support (set_val x)|)%N &&
    (point_support (set_val x) != finset.setT).
  apply/andP; split; first exact: point_support_positive.
  apply: boundary_support_proper; exact: set_valP.
pose A : proper_face := exist _ (point_support (set_val x)) hp.
exists A; first by [].
exists (support_point (set_val x)); first exact I.
have he : proper_face_simplex A = support_boundary_simplex x.
  apply: subcomplex_simplex_ext.
  have ep : proper_face_positive A = point_support_positive (set_val x) by apply: Prop_irrelevance.
  change (@face_inclusion n (point_support (set_val x)) (proper_face_positive A) =
    @face_inclusion n (point_support (set_val x)) (point_support_positive (set_val x))).
  by rewrite ep.
rewrite he. exact: boundary_evaluation_normal_form.
Qed.

Theorem realized_boundary_compact : @compact (realization_space Real D) setT.
Proof.
rewrite realized_boundary_finite_face_cover.
apply: bigsetU_compact => A _; exact: proper_face_image_compact.
Qed.

End Compactness.
End DPRealizationBoundaryCompact.
