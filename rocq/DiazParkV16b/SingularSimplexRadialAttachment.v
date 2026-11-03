(** Actual radial deformation of an arbitrary family's punctured attaching space. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalPushoutCarrier TopologicalPushoutDeformation SingularSimplexRadialFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPTopologicalPushoutCarrier
  DPTopologicalPushoutDeformation DPSingularSimplexRadialFamily.

Module DPSingularSimplexRadialAttachment.
Section Attachment.
Variable Real : realType.
Variable I : choiceType.
Variable d : I -> nat.
Variable X : topologicalType.
Variable j : hom topological_category (boundary_family Real d) X.

Definition radial_attaching_space := attaching_space (family_boundary_punctured Real d) j.

Lemma family_radial_retraction_at a :
  family_radial_projection Real d (family_boundary_punctured Real d a) = a.
Proof.
exact (congr1 (fun f : continuousType (boundary_family Real d) (boundary_family Real d) => f a)
  (family_radial_retraction Real d)).
Qed.

Definition radial_attaching_retraction : continuousType radial_attaching_space X :=
  @pushout_retraction (boundary_family Real d) (punctured_family Real d) X
    (family_boundary_punctured Real d) (family_radial_projection Real d)
    family_radial_retraction_at j.

Definition radial_attaching_homotopy : continuous_homotopy Real
  (continuous_identity radial_attaching_space)
  (continuous_compose radial_attaching_retraction (attaching_right_map (family_boundary_punctured Real d) j)) :=
  @pushout_deformation Real (boundary_family Real d) (punctured_family Real d) X
    (family_boundary_punctured Real d) (family_radial_projection Real d)
    family_radial_retraction_at (family_radial_homotopy Real d)
    (@family_radial_homotopy_fixed Real I d) j.

Lemma radial_attaching_retraction_right x :
  radial_attaching_retraction (attaching_right (family_boundary_punctured Real d) j x) = x.
Proof. exact: pushout_retraction_right. Qed.

Lemma radial_attaching_homotopy_fixed t x :
  homotopy_map radial_attaching_homotopy (t,attaching_right (family_boundary_punctured Real d) j x) =
    attaching_right (family_boundary_punctured Real d) j x.
Proof. exact: pushout_deformation_fixed. Qed.

End Attachment.
End DPSingularSimplexRadialAttachment.
