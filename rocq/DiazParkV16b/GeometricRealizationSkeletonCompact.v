(** Compact subsets and actual continuous maps into a geometric realization
    factor through one finite-dimensional skeleton. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology
  subtype_topology subspace_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialSkeleton TopologicalCategory
  TopologicalSimplexBasic TopologicalSimplexCompact
  GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationSkeletonTopology
  GeometricRealizationSkeletonSeparation TopologicalWeakFiltrationCompact TopologicalClosedImage.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import numFieldTopology.Exports.

Module DPRealizationSkeletonCompact.
Import DPSimplicialSet DPSimplicialSkeleton DPGeometricRealization DPGeometricRealizationMaps
  DPRealizationSkeletonTopology DPRealizationSkeletonSeparation
  DPTopologicalWeakFiltrationCompact DPTopologicalClosedImage.
Section Compactness.
Variable Real : realType.
Variable X : simplicial_set.

Theorem compact_in_realized_skeleton (K : set (realization_space Real X))
  (hK : compact K) : exists n, K `<=` range (realized_skeleton_inclusion Real X n).
Proof.
exact (@compact_in_weak_filtration (realization_space Real X)
  (fun n => realization_space Real (skeleton_set X n))
  (realized_skeleton_inclusion Real X)
  (fun n => @cts_fun _ _ (realized_skeleton_inclusion Real X n))
  (@realized_skeleton_range_mono Real X) (@realized_skeleton_cover Real X)
  (@realization_accessible Real X) (@realized_skeleton_weak_closed Real X) K hK).
Qed.

Theorem compact_map_in_realized_skeleton (Z : topologicalType) (hZ : @compact Z setT)
  (f : continuousType Z (realization_space Real X)) :
  exists n, forall z, range (realized_skeleton_inclusion Real X n) (f z).
Proof.
have hc : compact (range f).
  apply (@continuous_compact Z (realization_space Real X) f setT).
  - apply: continuous_subspaceT; exact: cts_fun.
  - exact hZ.
have [n hn] := compact_in_realized_skeleton hc.
exists n => z; apply hn; by exists z.
Qed.

Theorem compact_map_factors_skeleton (Z : topologicalType) (hZ : @compact Z setT)
  (f : continuousType Z (realization_space Real X)) :
  exists n (g : continuousType Z (realization_space Real (skeleton_set X n))),
    forall z, realized_skeleton_inclusion Real X n (g z) = f z.
Proof.
have [n hn] := compact_map_in_realized_skeleton hZ f.
exists n.
exists (@closed_image_lift _ _ (realized_skeleton_inclusion Real X n)
  (@actual_skeleton_inclusion_injective Real X n)
  (@actual_skeleton_inclusion_closed Real X n) Z f hn).
intro z; exact: closed_image_lift_equation.
Qed.

Theorem continuous_simplex_factors_skeleton n
  (f : continuousType (DPTopologicalSimplex.simplex_space Real n) (realization_space Real X)) :
  exists k (g : continuousType (DPTopologicalSimplex.simplex_space Real n)
    (realization_space Real (skeleton_set X k))),
    forall t, realized_skeleton_inclusion Real X k (g t) = f t.
Proof.
exact (@compact_map_factors_skeleton (DPTopologicalSimplex.simplex_space Real n)
  (@DPTopologicalSimplexCompact.simplex_compact Real n) f).
Qed.
End Compactness.
End DPRealizationSkeletonCompact.
