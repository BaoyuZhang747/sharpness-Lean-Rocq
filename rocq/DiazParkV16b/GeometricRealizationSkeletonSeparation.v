(** Actual closed skeletal inclusions and T1 separation, with every cell
    geometry hypothesis discharged by the proved boundary homeomorphisms. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory SimplicialSet SimplicialSubcomplex SimplicialSkeleton
  SimplicialSkeletonAttachmentStages SimplicialSkeletonAttachmentCover
  GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationSkeletonTopology
  GeometricRealizationSkeletonFinite GeometricRealizationSkeletonRelations
  GeometricRealizationCopowerBoundary TopologicalWeakFiltrationSeparation.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import numFieldTopology.Exports.

Module DPRealizationSkeletonSeparation.
Import DPSimplicialSet DPSimplicialSubcomplex DPSimplicialSkeleton
  DPSimplicialAttachmentStages DPSimplicialAttachmentCover
  DPGeometricRealization DPGeometricRealizationMaps DPRealizationSkeletonTopology
  DPRealizationSkeletonFinite DPRealizationSkeletonRelations
  DPGeometricRealizationCopowerBoundary DPTopologicalWeakFiltrationSeparation.
Section Separation.
Variable Real : realType.
Variable X : simplicial_set.

Lemma actual_boundary_injective n :
  injective (realization_map Real (attaching_inclusion X n)).
Proof.
exact (@realized_boundary_copower_injective Real (nondegenerate_cell X n) n).
Qed.

Lemma actual_boundary_closed n (S : set (realization_space Real (boundary_copower X n)))
  (hS : closed S) : closed (realization_map Real (attaching_inclusion X n) @` S).
Proof.
apply (@realized_boundary_copower_closed Real (nondegenerate_cell X n) n).
exact hS.
Qed.

Lemma actual_cells_accessible n : accessible_space (realization_space Real (cell_copower X n)).
Proof.
exact (@realized_cell_copower_accessible Real (nondegenerate_cell X n) n).
Qed.

Theorem actual_stage_accessible n : accessible_space (realization_space Real (stage_set X n)).
Proof.
refine (@realized_stage_accessible Real X _ _ _ n).
- exact actual_boundary_injective.
- intros k T hT; apply (@actual_boundary_closed k); exact hT.
- exact actual_cells_accessible.
Qed.

Theorem actual_skeleton_transition_injective n m (h : (n <= m)%N) :
  injective (realization_map Real (skeleton_transition X h)).
Proof.
exact (@realized_skeleton_transition_injective Real X actual_boundary_injective n m h).
Qed.

Theorem actual_skeleton_transition_closed n m (h : (n <= m)%N)
  (S : set (realization_space Real (skeleton_set X n))) (hS : closed S) :
  closed (realization_map Real (skeleton_transition X h) @` S).
Proof.
exact (@realized_skeleton_transition_closed Real X actual_boundary_injective
  actual_boundary_closed n m h S hS).
Qed.

Theorem actual_skeleton_inclusion_injective n :
  injective (realized_skeleton_inclusion Real X n).
Proof.
exact (@realized_skeleton_injective_of_transitions Real X
  actual_skeleton_transition_injective n).
Qed.

Lemma actual_skeleton_transition_inclusion n m (h : (n <= m)%N) z :
  realized_skeleton_inclusion Real X m (realization_map Real (skeleton_transition X h) z) =
  realized_skeleton_inclusion Real X n z.
Proof.
have e := realization_map_composition Real (skeleton_transition X h) (skeleton_inclusion X m).
rewrite skeleton_transition_inclusion in e.
exact (esym (f_equal (fun f : hom DPTopological.topological_category
  (realization_space Real (skeleton_set X n)) (realization_space Real X) => f z) e)).
Qed.

Theorem realization_accessible : accessible_space (realization_space Real X).
Proof.
apply (@weak_filtration_accessible (realization_space Real X)
  (fun n => realization_space Real (skeleton_set X n))
  (realized_skeleton_inclusion Real X) actual_skeleton_inclusion_injective
  (@realized_skeleton_weak_closed Real X)).
intro n; exact (@actual_stage_accessible n.+1).
Qed.

Theorem actual_skeleton_inclusion_closed n
  (S : set (realization_space Real (skeleton_set X n))) (hS : closed S) :
  closed (realized_skeleton_inclusion Real X n @` S).
Proof.
exact (@weak_filtration_stage_closed (realization_space Real X)
  (fun n => realization_space Real (skeleton_set X n))
  (realized_skeleton_inclusion Real X) actual_skeleton_inclusion_injective
  (@realized_skeleton_weak_closed Real X)
  (fun n m h => realization_map Real (skeleton_transition X h))
  actual_skeleton_transition_inclusion
  (fun n m h => @cts_fun _ _ (realization_map Real (skeleton_transition X h)))
  actual_skeleton_transition_closed n S hS).
Qed.
End Separation.
End DPRealizationSkeletonSeparation.
