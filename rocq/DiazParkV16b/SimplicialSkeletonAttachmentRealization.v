From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryLimits.
From DiazParkV16b Require Import SimplicialSetYoneda CategoryPushout
  SimplicialSkeletonAttachmentCover SimplicialSkeletonAttachmentPushout
  TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps
  GeometricRealizationColimits.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialAttachmentRealization.
Import DPSimplicialYoneda DPCategoryPushout DPSimplicialAttachmentCover
  DPSimplicialAttachmentPushout DPTopological DPGeometricRealization
  DPGeometricRealizationMaps DPGeometricRealizationColimits.

(** This is the actual realized span and its universal colimit, with literal
    characteristic and skeletal-inclusion legs. No topological embedding or
    singular-chain pushout preservation is asserted here. *)
Definition realized_skeletal_attachment_colimit (Real : realType) X n :
  colimiting_cocone (functor_comp
    (@span_diagram simplicial_category _ _ _ (attaching_inclusion X n) (attaching_map X n))
    (realization_functor Real)) :=
  realization_colimit Real (skeletal_attachment_colimit X n).

Lemma realized_skeletal_attachment_object (Real : realType) X n :
  colimit_object (realized_skeletal_attachment_colimit Real X n) =
    realization_space Real (stage_set X n.+1).
Proof. reflexivity. Qed.

Lemma realized_skeletal_attachment_cells (Real : realType) X n :
  cocone_leg (colimit_cocone (realized_skeletal_attachment_colimit Real X n)) span_left =
    realization_map Real (attaching_cells X n).
Proof. reflexivity. Qed.

Lemma realized_skeletal_attachment_stage (Real : realType) X n :
  cocone_leg (colimit_cocone (realized_skeletal_attachment_colimit Real X n)) span_right =
    realization_map Real (attaching_stage X n).
Proof. reflexivity. Qed.

End DPSimplicialAttachmentRealization.
