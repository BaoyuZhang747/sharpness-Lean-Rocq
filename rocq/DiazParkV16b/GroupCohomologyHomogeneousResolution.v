(** One shared homogeneous complex is a projective resolution after restriction
    to every subgroup.  All projectivity and exactness fields are proved. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryDiagramHomLimit CategoryEnoughProjectivesResolution.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousProjective.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPEnoughProjectiveResolutions
  DPGroupCohomologyHomogeneousComplex DPGroupCohomologyHomogeneousEquivariance
  DPGroupCohomologyHomogeneousProjective.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousResolution.
Section Resolution.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable H : {group G}.
Local Notation HS := [the finGroupType of [subg H]].
Local Notation C := (opposite (group_category HS)).

Definition homogeneous_d (n : nat) :
    nat_trans (homogeneous_diagram R H n.+1) (homogeneous_diagram R H n).
Proof.
refine (@Build_nat_trans C (module_category R)
  (homogeneous_diagram R H n.+1) (homogeneous_diagram R H n)
  (fun _ => module_hom_of_linear (homogeneous_boundary R G n)) _).
move=> x y a; apply module_hom_ext => v.
exact (@homogeneous_action_boundary R G n (val a) v).
Defined.

Definition homogeneous_aug :
    nat_trans (homogeneous_diagram R H 0) (constant_regular_diagram R C).
Proof.
refine (@Build_nat_trans C (module_category R)
  (homogeneous_diagram R H 0) (constant_regular_diagram R C)
  (fun _ => module_hom_of_linear (homogeneous_augmentation R G)) _).
move=> x y a; apply module_hom_ext => v.
exact (@homogeneous_action_augmentation R G (val a) v).
Defined.

Definition homogeneous_resolution : projective_resolution (constant_regular_diagram R C).
Proof.
refine (@Build_projective_resolution R C (constant_regular_diagram R C)
  (homogeneous_diagram R H) homogeneous_d homogeneous_aug
  (homogeneous_diagram_projective R H) _ _ _ _ _).
- move=> x r; exists (homogeneous_section R G r).
  exact (@homogeneous_augmentation_section R G r).
- move=> n x v; exact (@homogeneous_boundary_squared R G n v).
- move=> x v; exact (@homogeneous_augmentation_boundary R G v).
- move=> x v; split.
  + exact (@homogeneous_exact_zero R G v).
  + move=> [w <-]; exact (@homogeneous_augmentation_boundary R G w).
- move=> n x v; split.
  + exact (@homogeneous_exact_successor R G n v).
  + move=> [w <-]; exact (@homogeneous_boundary_squared R G n w).
Defined.

End Resolution.
Arguments homogeneous_resolution R {G} H.
End DPGroupCohomologyHomogeneousResolution.
