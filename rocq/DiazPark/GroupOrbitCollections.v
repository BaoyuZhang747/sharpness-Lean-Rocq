(** Full finite subcategories of the ordinary group orbit category. *)
From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite GroupOrbitCategory.
Import DPGroupOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPGroupOrbitCollection.
Section Collections.
Variable G : finGroupType.
Variable B : {group G} -> bool.

Definition object := {H : {group G} | B H}.
Definition finite_category : CategoryFinite.finite_category.
Proof.
  refine (@Build_finite_category [the finType of object]
    (fun H K => [the finType of DPGroupOrbit.orbit_hom (val H) (val K)])
    (fun H => DPGroupOrbit.orbit_identity (val H))
    (fun H K L f g => DPGroupOrbit.orbit_compose f g) _ _ _).
  - intros H K f. exact (@compose_id_left (DPGroupOrbit.orbit_category G) _ _ f).
  - intros H K f. exact (@compose_id_right (DPGroupOrbit.orbit_category G) _ _ f).
  - intros H K L U f g h. exact (@compose_assoc (DPGroupOrbit.orbit_category G) _ _ _ _ f g h).
Defined.
Definition category := fc_category finite_category.

Definition inclusion : functor category (DPGroupOrbit.orbit_category G).
Proof. refine (@Build_functor category (DPGroupOrbit.orbit_category G)
  (fun H => val H) (fun H K f => f) _ _); reflexivity. Defined.

End Collections.
End DPGroupOrbitCollection.
