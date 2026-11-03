(** The actual homogeneous terms, restricted to any subgroup, are free
    diagrams and therefore projective over every coefficient ring. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso CategoryEnoughProjectives BarFreeModule BarResolutionHom.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousPaths
  GroupCohomologyHomogeneousProjectiveCoordinates.
Import GRing.Theory DiazParkFreeModule DiazParkBarResolutionHom DPEnoughProjectives
  DPGroupCohomology DPGroupCohomologyHomogeneousPaths
  DPGroupCohomologyHomogeneousProjectiveCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousProjective.

Lemma projective_of_isomorphism (C : category) (P Q : C)
    (e : @isomorphism C P Q) : projective_object C P -> projective_object C Q.
Proof.
move=> hP X Y q hq a.
have [b hb] := hP X Y q hq (compose (iso_hom e) a).
exists (compose (iso_inv e) b).
by rewrite compose_assoc hb -compose_assoc iso_inv_hom compose_id_left.
Qed.

Section Projective.
Variable R : pzRingType.
Variable G : finGroupType.
Variable H : {group G}.
Variable n : nat.
Local Notation HS := [subg H]%type.
Local Notation C := (opposite (group_category [the finGroupType of HS])).

Definition homogeneous_diagram : module_diagram R C.
Proof.
refine (@Build_functor C (module_category R)
  (fun _ => free_module R (homogeneous_generator G n))
  (fun x y a => module_hom_of_linear (free_map R (left_translate n.+1 (val a)))) _ _).
- move=> x; apply free_module_hom_ext=> v.
  change (free_map R (left_translate n.+1 1%g) (free_basis R v) = free_basis R v).
  by rewrite free_map_basis left_translate_identity.
- move=> x y z a b; apply free_module_hom_ext=> v.
  change (free_map R (left_translate n.+1 (val (b * a)%g)) (free_basis R v) =
    free_map R (left_translate n.+1 (val b))
      (free_map R (left_translate n.+1 (val a)) (free_basis R v))).
  by rewrite !free_map_basis left_translate_composition.
Defined.

Lemma homogeneous_diagram_action x y (a : hom C x y)
    (v : free_module R (homogeneous_generator G n)) :
  module_hom_fun (fmap homogeneous_diagram a) v =
    free_map R (left_translate n.+1 (val a)) v.
Proof. reflexivity. Qed.

Definition orbit_base (_ : orbit_index H n) : C := tt.
Definition free_orbit_diagram : module_diagram R C := free_diagram R orbit_base.

Definition generator_to_homogeneous (x : C) (a : free_generator orbit_base x) :
    homogeneous_generator G n :=
  match a with existT i h => expand (i,h) end.

Definition homogeneous_to_generator (x : C) (v : homogeneous_generator G n) :
    free_generator orbit_base x :=
  existT _ (coordinates H v).1 (coordinates H v).2.

Lemma generator_homogeneous_inverse x (a : free_generator orbit_base x) :
  homogeneous_to_generator x (generator_to_homogeneous a) = a.
Proof.
case: a=> i h; change (existT _ (coordinates H (expand (i,h))).1
  (coordinates H (expand (i,h))).2 = existT _ i h).
by rewrite coordinates_expand.
Qed.

Lemma homogeneous_generator_inverse x (v : homogeneous_generator G n) :
  generator_to_homogeneous (homogeneous_to_generator x v) = v.
Proof.
change (expand ((coordinates H v).1, (coordinates H v).2) = v).
rewrite -surjective_pairing; exact: expand_coordinates.
Qed.

Lemma generator_to_homogeneous_natural x y (a : hom C x y)
    (v : free_generator orbit_base x) :
  generator_to_homogeneous (generator_postcompose a v) =
    left_translate n.+1 (val a) (generator_to_homogeneous v).
Proof.
case: v=> i h.
change (expand (i, (a * h)%g) = left_translate n.+1 (val a) (expand (i,h))).
exact: (expand_translate a (i,h)).
Qed.

Definition homogeneous_free_component (x : C) :
    @isomorphism (module_category R)
      (fobj free_orbit_diagram x) (fobj homogeneous_diagram x).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (free_map R (@generator_to_homogeneous x)))
  (module_hom_of_linear (free_map R (homogeneous_to_generator x))) _ _).
- apply free_module_hom_ext=> v.
  change (free_map R (homogeneous_to_generator x)
    (free_map R (@generator_to_homogeneous x) (free_basis R v)) = free_basis R v).
  by rewrite !free_map_basis generator_homogeneous_inverse.
- apply free_module_hom_ext=> v.
  change (free_map R (@generator_to_homogeneous x)
    (free_map R (homogeneous_to_generator x) (free_basis R v)) = free_basis R v).
  by rewrite !free_map_basis homogeneous_generator_inverse.
Defined.

Definition homogeneous_free_iso :
    @isomorphism (functor_category C (module_category R)) free_orbit_diagram homogeneous_diagram.
Proof.
refine (@nat_iso_of_components C (module_category R)
  free_orbit_diagram homogeneous_diagram homogeneous_free_component _).
move=> x y a; apply free_module_hom_ext=> v.
change (free_map R (@generator_to_homogeneous y)
  (free_map R (generator_postcompose a) (free_basis R v)) =
  free_map R (left_translate n.+1 (val a))
    (free_map R (@generator_to_homogeneous x) (free_basis R v))).
by rewrite !free_map_basis generator_to_homogeneous_natural.
Defined.

Theorem homogeneous_diagram_projective :
  projective_object (functor_category C (module_category R)) homogeneous_diagram.
Proof.
apply: (projective_of_isomorphism homogeneous_free_iso).
exact: free_diagram_projective.
Qed.

End Projective.

Arguments homogeneous_diagram R {G} H n.
Arguments homogeneous_diagram_projective R {G} H n.

End DPGroupCohomologyHomogeneousProjective.

Print Assumptions DPGroupCohomologyHomogeneousProjective.homogeneous_free_iso.
Print Assumptions DPGroupCohomologyHomogeneousProjective.homogeneous_diagram_projective.
