(** Literal-map normal form of the already constructed actual skeletal pushout. *)
From mathcomp Require Import reals.
From DiazParkV16b Require Import CategoryPushout SimplicialSet
  SimplicialSkeletonAttachmentCover GeometricRealizationMaps
  GeometricRealizationSkeletonTopology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module DPRealizationSkeletonPushout.
Import DPCategoryPushout DPSimplicialAttachmentCover DPGeometricRealizationMaps.
Theorem actual_skeletal_attachment_pushout (Real : realType)
  (X : DPSimplicialSet.simplicial_set) n :
  pushout_square (realization_map Real (attaching_inclusion X n))
    (realization_map Real (attaching_map X n))
    (realization_map Real (attaching_cells X n))
    (realization_map Real (attaching_stage X n)).
Proof. exact (DPRealizationSkeletonTopology.realized_skeletal_attachment_pushout Real X n). Qed.
End DPRealizationSkeletonPushout.
