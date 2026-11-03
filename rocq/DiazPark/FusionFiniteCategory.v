From mathcomp Require Import all_boot all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite FusionMaps FusionSystems FusionOrbit.
Import DPFusion DPFusionSystem DPFusionOrbit.

(** The finite presentations use exactly the existing fusion orbit objects
    and quotient morphisms, with identity-on-data comparison functors. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPFusionFinite.
Section FiniteOrbit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition orbit_finite_category : finite_category.
Proof.
refine {| fc_object := [the finType of {group S}];
          fc_hom := fun P Q => [the finType of DPFusionOrbit.orbit_hom F P Q];
          fc_identity := DPFusionOrbit.orbit_identity F;
          fc_compose := fun P Q T f g => @DPFusionOrbit.orbit_compose S F P Q T f g |}.
- move=> P Q f; exact (@Category.compose_id_left (DPFusionOrbit.orbit_category F) P Q f).
- move=> P Q f; exact (@Category.compose_id_right (DPFusionOrbit.orbit_category F) P Q f).
- move=> P Q T U f g h; exact (@Category.compose_assoc (DPFusionOrbit.orbit_category F) P Q T U f g h).
Defined.

Definition finite_to_orbit :
    functor (fc_category orbit_finite_category) (DPFusionOrbit.orbit_category F).
Proof.
refine (@Build_functor (fc_category orbit_finite_category) (DPFusionOrbit.orbit_category F)
  (fun P => P) (fun P Q f => f) _ _); reflexivity.
Defined.

Definition orbit_to_finite :
    functor (DPFusionOrbit.orbit_category F) (fc_category orbit_finite_category).
Proof.
refine (@Build_functor (DPFusionOrbit.orbit_category F) (fc_category orbit_finite_category)
  (fun P => P) (fun P Q f => f) _ _); reflexivity.
Defined.

Definition centric_finite_category : finite_category.
Proof.
refine {| fc_object := [the finType of DPFusionOrbit.centric_object F];
          fc_hom := fun P Q => [the finType of DPFusionOrbit.orbit_hom F (val P) (val Q)];
          fc_identity := fun P => DPFusionOrbit.orbit_identity F (val P);
          fc_compose := fun P Q T f g =>
            @DPFusionOrbit.orbit_compose S F (val P) (val Q) (val T) f g |}.
- move=> P Q f; exact (@Category.compose_id_left (DPFusionOrbit.centric_orbit_category F) P Q f).
- move=> P Q f; exact (@Category.compose_id_right (DPFusionOrbit.centric_orbit_category F) P Q f).
- move=> P Q T U f g h; exact (@Category.compose_assoc (DPFusionOrbit.centric_orbit_category F) P Q T U f g h).
Defined.

Definition finite_to_centric :
    functor (fc_category centric_finite_category) (DPFusionOrbit.centric_orbit_category F).
Proof.
refine (@Build_functor (fc_category centric_finite_category)
  (DPFusionOrbit.centric_orbit_category F)
  (fun P => P) (fun P Q f => f) _ _); reflexivity.
Defined.

Definition centric_to_finite :
    functor (DPFusionOrbit.centric_orbit_category F) (fc_category centric_finite_category).
Proof.
refine (@Build_functor (DPFusionOrbit.centric_orbit_category F)
  (fc_category centric_finite_category)
  (fun P => P) (fun P Q f => f) _ _); reflexivity.
Defined.

End FiniteOrbit.
End DPFusionFinite.

Print Assumptions DPFusionFinite.orbit_finite_category.
Print Assumptions DPFusionFinite.centric_finite_category.
Print Assumptions DPFusionFinite.finite_to_centric.
