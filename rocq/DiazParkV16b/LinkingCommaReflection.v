(** A concrete reflection of the actual linking/orbit comma category
    into the one-object category of the named subgroup. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection
  LinkingCommaCategory LinkingCommaFibres GroupCohomologyBase.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingOrbit DPLinkingComma DPLinkingCommaFibres DPGroupCohomology.
Local Open Scope group_scope.

Module DPLinkingCommaReflection.
Section Reflection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation C := (subgroup_comma L P).
Local Notation B := (subgroup_comparison_object L P).

Definition base (X : C) : linking_hom L (costructured_source X) P :=
  lift_orbit_arrow L (costructured_arrow X).

Lemma base_projection (X : C) : fmap (orbit_projection L) (base X) = costructured_arrow X.
Proof. exact: orbit_projection_lift. Qed.

Definition base_arrow (X : C) : hom C X B.
Proof.
refine (@Build_costructured_hom (linking_category L) (DPFusionOrbit.centric_orbit_category F)
  (orbit_projection L) P X B (base X) _).
rewrite compose_id_right; exact: base_projection.
Defined.

Definition coordinate_lift (X : C) (f : linking_hom L (costructured_source X) P)
    (hf : fmap (orbit_projection L) f = costructured_arrow X) :
    {z : [subg (val P)] | linking_compose L (base X) (distinguished L z) = f}.
Proof.
apply: cid.
have [z [hz _]] := @orbit_fiber S F L (costructured_source X) P (base X) f
  (eq_trans (base_projection X) (esym hf)).
by exists z.
Defined.

Definition coordinate (X : C) (f : linking_hom L (costructured_source X) P)
    (hf : fmap (orbit_projection L) f = costructured_arrow X) : [subg (val P)] :=
  proj1_sig (coordinate_lift hf).

Lemma coordinate_spec (X : C) (f : linking_hom L (costructured_source X) P)
    (hf : fmap (orbit_projection L) f = costructured_arrow X) :
    linking_compose L (base X) (distinguished L (coordinate hf)) = f.
Proof. exact: proj2_sig (coordinate_lift hf). Qed.

Lemma reflection_projection (X Y : C) (u : hom C X Y) :
    fmap (orbit_projection L) (linking_compose L (costructured_map u) (base Y)) =
    costructured_arrow X.
Proof.
change (fmap (orbit_projection L) (@compose (linking_category L) _ _ _
  (costructured_map u) (base Y)) = costructured_arrow X).
rewrite fmap_compose base_projection; exact: costructured_commutes.
Qed.

Definition reflection_map (X Y : C) (u : hom C X Y) : [subg (val P)] :=
  coordinate (reflection_projection u).

Lemma reflection_triangle (X Y : C) (u : hom C X Y) :
    linking_compose L (base X) (distinguished L (reflection_map u)) =
    linking_compose L (costructured_map u) (base Y).
Proof. exact: coordinate_spec. Qed.

Lemma reflection_identity (X : C) : reflection_map (@identity C X) = 1.
Proof.
apply: (@distinguished_post_injective S F L (costructured_source X) P (base X)).
rewrite reflection_triangle distinguished_one.
change (linking_compose L (linking_identity L (costructured_source X)) (base X) =
  linking_compose L (base X) (linking_identity L P)).
by rewrite linking_id_left linking_id_right.
Qed.

Lemma reflection_compose (X Y Z : C) (u : hom C X Y) (v : hom C Y Z) :
    reflection_map (@compose C X Y Z u v) = reflection_map u * reflection_map v.
Proof.
apply: (@distinguished_post_injective S F L (costructured_source X) P (base X)).
rewrite reflection_triangle -distinguished_compose -linking_assoc reflection_triangle.
change (linking_compose L (linking_compose L (costructured_map u) (costructured_map v))
    (base Z) =
  linking_compose L (linking_compose L (costructured_map u) (base Y))
    (distinguished L (reflection_map v))).
by rewrite !linking_assoc reflection_triangle.
Qed.

Definition reflection : functor C (group_category [subg (val P)]%type).
Proof.
refine (@Build_functor C (group_category [subg (val P)]%type)
  (fun _ => tt) (fun X Y u => reflection_map u) _ _).
- exact: reflection_identity.
- exact: reflection_compose.
Defined.

Definition reflection_unit :
    nat_trans (functor_id C) (functor_comp reflection (subgroup_comparison L P)).
Proof.
refine (@Build_nat_trans C C (functor_id C)
  (functor_comp reflection (subgroup_comparison L P)) base_arrow _).
move=> X Y u; apply costructured_hom_ext.
symmetry; exact: reflection_triangle.
Defined.
End Reflection.
End DPLinkingCommaReflection.

Check DPLinkingCommaReflection.reflection.
Check DPLinkingCommaReflection.reflection_unit.
Print Assumptions DPLinkingCommaReflection.reflection.
Print Assumptions DPLinkingCommaReflection.reflection_unit.
