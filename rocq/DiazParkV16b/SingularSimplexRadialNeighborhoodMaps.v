(** The literal map from punctured radial attachments into full cell attachments. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout CategoryPushoutPasting
  TopologicalPushoutCarrier TopologicalPushoutUniversal TopologicalCoproductSubspaceImages
  TopologicalSimplexBasic SingularSimplexRadialContinuity SingularSimplexRadialDeformationGeometry
  SingularSimplexRadialFamily SingularSimplexRadialAttachment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPCategoryPushout DPCategoryPushoutPasting
  DPTopologicalPushoutCarrier DPTopologicalPushoutUniversal DPTopologicalCoproductSubspaceImages
  DPTopologicalSimplex DPSingularSimplexRadialContinuity DPSingularSimplexRadialDeformationGeometry
  DPSingularSimplexRadialFamily DPSingularSimplexRadialAttachment.
Local Open Scope classical_set_scope.

Module DPSingularSimplexRadialNeighborhoodMaps.
Section Neighborhood.
Variable Real : realType.
Variable I : choiceType.
Variable d : I -> nat.
Variable X : topologicalType.
Variable j : hom topological_category (boundary_family Real d) X.

Definition full_radial_attachment := attaching_space (family_boundary_inclusion Real d) j.

Lemma punctured_family_inclusion_injective : injective (family_punctured_inclusion Real d).
Proof.
exact (@family_subspace_inclusion_injective I (fun i => simplex_space Real (d i))
  (fun i => @punctured_set Real (d i))).
Qed.

Lemma punctured_family_inclusion_open (S : set (punctured_family Real d)) (hS : open S) :
  open (family_punctured_inclusion Real d @` S).
Proof.
apply: (@family_subspace_inclusion_open I (fun i => simplex_space Real (d i))
  (fun i => @punctured_set Real (d i))) => // i.
exact: punctured_set_open.
Qed.

Definition full_attachment_factored_pushout : @pushout_square topological_category
  (boundary_family Real d) (cell_family Real d) X full_radial_attachment
  (continuous_compose (family_boundary_punctured Real d) (family_punctured_inclusion Real d)) j
  (attaching_left_map (family_boundary_inclusion Real d) j)
  (attaching_right_map (family_boundary_inclusion Real d) j).
Proof.
rewrite family_boundary_factorization; exact: attaching_pushout.
Defined.

Definition radial_neighborhood_map : hom topological_category
    (@radial_attaching_space Real I d X j) full_radial_attachment :=
  pasting_map (attaching_pushout (family_boundary_punctured Real d) j)
    full_attachment_factored_pushout.

Lemma radial_neighborhood_map_left n :
  radial_neighborhood_map (attaching_left (family_boundary_punctured Real d) j n) =
    attaching_left (family_boundary_inclusion Real d) j (family_punctured_inclusion Real d n).
Proof.
exact (congr1 (fun f : hom topological_category (punctured_family Real d) full_radial_attachment => f n)
  (pasting_map_left (attaching_pushout (family_boundary_punctured Real d) j)
    full_attachment_factored_pushout)).
Qed.

Lemma radial_neighborhood_map_right x :
  radial_neighborhood_map (attaching_right (family_boundary_punctured Real d) j x) =
    attaching_right (family_boundary_inclusion Real d) j x.
Proof.
exact (congr1 (fun f : hom topological_category X full_radial_attachment => f x)
  (pasting_map_right (attaching_pushout (family_boundary_punctured Real d) j)
    full_attachment_factored_pushout)).
Qed.

Definition radial_neighborhood_pushout : @pushout_square topological_category
  (punctured_family Real d) (cell_family Real d) (@radial_attaching_space Real I d X j) full_radial_attachment
  (family_punctured_inclusion Real d)
  (attaching_left_map (family_boundary_punctured Real d) j)
  (attaching_left_map (family_boundary_inclusion Real d) j)
  radial_neighborhood_map :=
  pasting_square (attaching_pushout (family_boundary_punctured Real d) j)
    full_attachment_factored_pushout.

End Neighborhood.
End DPSingularSimplexRadialNeighborhoodMaps.
