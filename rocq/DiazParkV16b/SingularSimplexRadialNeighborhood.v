(** The genuine open neighborhood furnished by a family of radial collars. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalPushoutCarrier
  TopologicalPushoutEmbedding SingularSimplexRadialFamily SingularSimplexRadialAttachment
  SingularSimplexRadialNeighborhoodMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalPushoutCarrier DPTopologicalPushoutEmbedding
  DPSingularSimplexRadialFamily DPSingularSimplexRadialAttachment DPSingularSimplexRadialNeighborhoodMaps.
Local Open Scope classical_set_scope.

Module DPSingularSimplexRadialNeighborhood.
Section Neighborhood.
Variable Real : realType.
Variable I : choiceType.
Variable d : I -> nat.
Variable X : topologicalType.
Variable j : hom topological_category (boundary_family Real d) X.

Definition radial_neighborhood : set (@full_radial_attachment Real I d X j) :=
  radial_neighborhood_map j @` [set: @radial_attaching_space Real I d X j].

Lemma radial_neighborhood_injective : injective (radial_neighborhood_map j).
Proof. exact: (pushout_right_injective (radial_neighborhood_pushout j) (@punctured_family_inclusion_injective Real I d)). Qed.

Lemma radial_neighborhood_open_image (S : set (@radial_attaching_space Real I d X j))
    (hS : open S) : open (radial_neighborhood_map j @` S).
Proof.
apply: (pushout_right_open_image (radial_neighborhood_pushout j)
  (@punctured_family_inclusion_injective Real I d) (@punctured_family_inclusion_open Real I d) hS).
Qed.

Theorem radial_neighborhood_open : open radial_neighborhood.
Proof. exact: radial_neighborhood_open_image openT. Qed.

Theorem radial_neighborhood_cell_preimage :
  attaching_left (family_boundary_inclusion Real d) j @^-1` radial_neighborhood =
    @family_punctured_set Real I d.
Proof.
rewrite /radial_neighborhood (pushout_left_preimage_right_image (radial_neighborhood_pushout j)
  (@punctured_family_inclusion_injective Real I d)).
rewrite preimage_setT; exact: family_punctured_range.
Qed.

Theorem radial_neighborhood_contains_old x :
  radial_neighborhood (attaching_right (family_boundary_inclusion Real d) j x).
Proof.
exists (attaching_right (family_boundary_punctured Real d) j x); first by [].
exact: radial_neighborhood_map_right.
Qed.

End Neighborhood.
End DPSingularSimplexRadialNeighborhood.
