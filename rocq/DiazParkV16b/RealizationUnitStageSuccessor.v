(** The actual skeletal attachment step for the realization-unit theorem. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialSubcomplex SimplicialNondegenerate
  SimplicialBoundary SimplicialSkeletonAttachmentStages SimplicialSkeletonAttachmentCover SimplicialAttachmentRelativeChains
  SimplicialChainsMaps GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationSkeletonTopology
  GeometricRealizationCopowerBoundary TopologicalCategory TopologicalPushoutEmbedding
  SingularCohomology SingularRelativePairs SingularRadialAttachmentCoordinates
  ChainComplex ChainMapImage ChainRelativePairs ChainQuasiIsomorphism ChainQuasiIsomorphismLaws
  RealizationUnitChains RealizationUnitCopower RealizationUnitStandardCopower RealizationUnitAttachment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialSet DPSimplicialSubcomplex DPSimplicialNondegenerate DPSimplicialBoundary
  DPSimplicialAttachmentStages DPSimplicialAttachmentCover DPSimplicialAttachmentRelativeChains DPSimplicialChainMaps
  DPGeometricRealization DPGeometricRealizationMaps DPRealizationSkeletonTopology
  DPGeometricRealizationCopowerBoundary DPTopological DPTopologicalPushoutEmbedding
  DPSingularCohomology DPSingularRelativePairs DPSingularRadialAttachmentCoordinates
  DPChainComplex DPChainMapImage DPChainRelativePairs DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPRealizationUnitChains DPRealizationUnitCopower DPRealizationUnitStandardCopower DPRealizationUnitAttachment.
Module DPRealizationUnitStageSuccessor.
Section Stage.
Variable Real : realType.
Variable R : pzRingType.
Variable X : simplicial_set.
Variable n : nat.

Lemma stage_attaching_inclusion_injective k : injective (component (attaching_inclusion X n) k).
Proof.
move=> [a f] [b g].
change ((a,proj1_sig f) = (b,proj1_sig g) -> (a,f) = (b,g)) => h.
have ab : a = b := congr1 fst h; subst b.
congr (a,_); apply: subcomplex_simplex_ext; exact: (congr1 snd h).
Qed.
Lemma stage_attaching_stage_injective k : injective (component (attaching_stage X n) k).
Proof.
move=> x y h; apply: subcomplex_simplex_ext; exact: (congr1 (@proj1_sig _ _) h).
Qed.

Let hpush := realized_skeletal_attachment_pushout Real X n.
Let ri := realization_map Real (attaching_inclusion X n).
Let rp := realization_map Real (attaching_map X n).
Let rq := realization_map Real (attaching_cells X n).
Let rj := realization_map Real (attaching_stage X n).

Lemma stage_realized_inclusion_injective : injective ri.
Proof. exact (@realized_boundary_copower_injective Real (nondegenerate_cell X n) n). Qed.
Lemma stage_realized_stage_injective : injective rj.
Proof. exact (pushout_right_injective hpush stage_realized_inclusion_injective). Qed.

Lemma stage_simplicial_relative_quasi_isomorphism : quasi_isomorphism
  (@simplicial_attachment_relative R _ _ _ _ (attaching_inclusion X n) (attaching_map X n)
    (attaching_cells X n) (attaching_stage X n) (attaching_square X n)).
Proof.
apply: (@quasi_isomorphism_ext R _ _ (attachment_relative_map R X n)); last exact: attachment_relative_quasi_isomorphism.
move=> k x; have [b <-] := @relative_projection_surjective R _ _ (chain_map_of R (attaching_inclusion X n)) k x.
by rewrite attachment_relative_map_projection /simplicial_attachment_relative relative_pair_map_projection.
Qed.

Lemma stage_singular_relative_quasi_isomorphism : quasi_isomorphism
  (@singular_attachment_relative Real R _ _ _ _ (attaching_inclusion X n) (attaching_map X n)
    (attaching_cells X n) (attaching_stage X n) (attaching_square X n)).
Proof.
pose eA := realized_boundaries_coordinates Real (nondegenerate_cell X n) n.
pose eB := realized_cells_coordinates Real (nondegenerate_cell X n) n.
have hq := @coordinate_attachment_relative_quasi_isomorphism Real R
  [the choiceType of {classic (nondegenerate_cell X n)}] (fun _ => n)
  _ _ _ _ ri rp rq rj hpush eA eB
  (@realized_boundary_copower_square Real (nondegenerate_cell X n) n).
apply: (@quasi_isomorphism_ext R _ _ (@coordinate_attachment_relative Real R _ _ _ _ ri rp rq rj hpush)); last exact hq.
move=> k x; have [b <-] := @relative_projection_surjective R _ _ (singular_chain_map Real R ri) k x.
rewrite /coordinate_attachment_relative
  (@singular_relative_map_projection Real R _ _ _ _ ri rj rp rq
    (@coordinate_original_square _ _ _ _ ri rp rq rj hpush))
  /singular_attachment_relative
  (@singular_relative_map_projection Real R _ _ _ _ ri rj rp rq
    (@realized_attachment_square Real _ _ _ _ (attaching_inclusion X n) (attaching_map X n)
      (attaching_cells X n) (attaching_stage X n) (attaching_square X n))).
reflexivity.
Qed.

Theorem stage_successor_unit_quasi_isomorphism
    (hboundary : quasi_isomorphism (realization_unit_chains Real R (boundary_set n)))
    (hstage : quasi_isomorphism (realization_unit_chains Real R (stage_set X n))) :
    quasi_isomorphism (realization_unit_chains Real R (stage_set X n.+1)).
Proof.
apply: (@realization_unit_attachment_quasi_isomorphism Real R _ _ _ _
  (attaching_inclusion X n) (attaching_map X n) (attaching_cells X n) (attaching_stage X n)
  (attaching_square X n)).
- exact: stage_attaching_inclusion_injective.
- exact: stage_attaching_stage_injective.
- exact: stage_realized_inclusion_injective.
- exact: stage_realized_stage_injective.
- exact (@realization_unit_copower_quasi_isomorphism Real R (nondegenerate_cell X n) (boundary_set n) hboundary).
- exact (@standard_copower_unit_quasi_isomorphism Real R (nondegenerate_cell X n) n).
- exact hstage.
- exact: stage_simplicial_relative_quasi_isomorphism.
- exact: stage_singular_relative_quasi_isomorphism.
Qed.
End Stage.
End DPRealizationUnitStageSuccessor.
