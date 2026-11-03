(** Concrete complementary opens and overlaps for arbitrary radial cell attachments. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic TopologicalSimplexFaces
  TopologicalPushoutCarrier TopologicalPushoutUniversal TopologicalPushoutComplement TopologicalPushoutOverlap
  TopologicalCoproductSubspaceImages SingularSimplexRadialCoordinates SingularSimplexRadialContinuity
  SingularSimplexRadialFamily SingularSimplexRadialNeighborhoodMaps SingularSimplexRadialNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalSimplex DPTopologicalSimplexFaces
  DPTopologicalPushoutCarrier DPTopologicalPushoutUniversal DPTopologicalPushoutComplement DPTopologicalPushoutOverlap
  DPTopologicalCoproductSubspaceImages DPSingularSimplexRadialCoordinates DPSingularSimplexRadialContinuity
  DPSingularSimplexRadialFamily DPSingularSimplexRadialNeighborhoodMaps DPSingularSimplexRadialNeighborhood.
Local Open Scope classical_set_scope.

Module DPSingularSimplexRadialComplement.
Section Complement.
Variable Real : realType.
Variable I : choiceType.
Variable d : I -> nat.
Variable X : topologicalType.
Variable j : hom topological_category (boundary_family Real d) X.

Lemma boundary_family_inclusion_injective : injective (family_boundary_inclusion Real d).
Proof.
exact (@family_subspace_inclusion_injective I (fun i => simplex_space Real (d i))
  (fun i => @boundary_set Real (d i))).
Qed.
Lemma boundary_family_inclusion_closed (S : set (boundary_family Real d)) (hS : closed S) :
  closed (family_boundary_inclusion Real d @` S).
Proof.
apply: (@family_subspace_inclusion_closed I (fun i => simplex_space Real (d i))
  (fun i => @boundary_set Real (d i))) => // i.
exact: boundary_set_closed.
Qed.

Definition radial_cell_complement := @source_complement _ _ (family_boundary_inclusion Real d).
Definition radial_attachment_complement := @target_complement _ _ (attaching_right_map (family_boundary_inclusion Real d) j).

Lemma radial_cell_complement_open : open radial_cell_complement.
Proof. exact: (@source_complement_open _ _ (family_boundary_inclusion Real d) boundary_family_inclusion_closed). Qed.
Lemma radial_attachment_complement_open : open radial_attachment_complement.
Proof.
exact: (target_complement_open (attaching_pushout (family_boundary_inclusion Real d) j)
  boundary_family_inclusion_injective boundary_family_inclusion_closed).
Qed.

Definition radial_complement_homeomorphism :=
  @pushout_complement_homeomorphism _ _ _ _ (family_boundary_inclusion Real d) j
    (attaching_left_map (family_boundary_inclusion Real d) j)
    (attaching_right_map (family_boundary_inclusion Real d) j)
    (attaching_pushout (family_boundary_inclusion Real d) j)
    boundary_family_inclusion_injective boundary_family_inclusion_closed.

Lemma radial_overlap_correspondence b : @family_punctured_set Real I d b <->
  @radial_neighborhood Real I d X j (attaching_left (family_boundary_inclusion Real d) j b).
Proof.
change (@family_punctured_set Real I d b <->
  (attaching_left (family_boundary_inclusion Real d) j @^-1` @radial_neighborhood Real I d X j) b).
by rewrite radial_neighborhood_cell_preimage.
Qed.

Definition radial_overlap_homeomorphism :=
  @pushout_overlap_homeomorphism _ _ _ _ (family_boundary_inclusion Real d) j
    (attaching_left_map (family_boundary_inclusion Real d) j)
    (attaching_right_map (family_boundary_inclusion Real d) j)
    (attaching_pushout (family_boundary_inclusion Real d) j)
    boundary_family_inclusion_injective boundary_family_inclusion_closed
    (@family_punctured_set Real I d) (@radial_neighborhood Real I d X j) radial_overlap_correspondence.

Lemma radial_complement_homeomorphism_val b :
  val (iso_hom radial_complement_homeomorphism b) = attaching_left (family_boundary_inclusion Real d) j (val b).
Proof. reflexivity. Qed.
Lemma radial_overlap_homeomorphism_val b :
  val (iso_hom radial_overlap_homeomorphism b) = attaching_left (family_boundary_inclusion Real d) j (val b).
Proof. reflexivity. Qed.

Theorem radial_cell_cover b : @family_punctured_set Real I d b \/ radial_cell_complement b.
Proof.
case: (pselect ((family_boundary_inclusion Real d @` [set: boundary_family Real d]) b)) => hb.
- left; case: hb => [[a x] _ <-].
  change (@punctured_set Real (d a) (val x)); exact: boundary_not_uniform (set_valP x).
- by right.
Qed.

Theorem radial_attachment_cover y : @radial_neighborhood Real I d X j y \/ radial_attachment_complement y.
Proof.
case: (pselect ((attaching_right_map (family_boundary_inclusion Real d) j @` [set: X]) y)) => hy.
- left; case: hy => [x _ <-]; exact: radial_neighborhood_contains_old.
- by right.
Qed.

End Complement.
End DPSingularSimplexRadialComplement.
