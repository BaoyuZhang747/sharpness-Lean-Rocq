(** The actual linking comma reflection is left adjoint to the actual
    distinguished subgroup comparison.  Both triangles are proved. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryComma CategoryAdjunction FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection LinkingCommaCategory
  LinkingCommaFibres LinkingCommaReflection GroupCohomologyBase.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingOrbit DPLinkingComma DPLinkingCommaFibres
  DPLinkingCommaReflection DPGroupCohomology.
Local Open Scope group_scope.

Module DPLinkingCommaAdjunction.
Section Adjunction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation C := (subgroup_comma L P).
Local Notation G := (group_category [subg (val P)]%type).
Local Notation B := (subgroup_comparison_object L P).
Local Notation J := (subgroup_comparison L P).
Local Notation R := (reflection L P).

Lemma counit_projection : fmap (orbit_projection L) (linking_identity L P) = costructured_arrow B.
Proof. exact: fmap_id. Qed.

Definition counit_element : [subg (val P)] :=
  @coordinate S F L P B (linking_identity L P) counit_projection.

Lemma counit_triangle :
    linking_compose L ((@base S F L P B)) (distinguished L counit_element) = linking_identity L P.
Proof. exact: coordinate_spec. Qed.

Lemma counit_natural (a : [subg (val P)]) :
    @reflection_map S F L P B B (subgroup_comparison_arrow L a) * counit_element =
    counit_element * a.
Proof.
apply: (@distinguished_post_injective S F L P P ((@base S F L P B))).
rewrite -!distinguished_compose -!linking_assoc.
rewrite (@reflection_triangle S F L P B B (subgroup_comparison_arrow L a)).
change (linking_compose L (linking_compose L (distinguished L a) ((@base S F L P B)))
    (distinguished L counit_element) =
  linking_compose L (linking_compose L ((@base S F L P B)) (distinguished L counit_element))
    (distinguished L a)).
by rewrite linking_assoc !counit_triangle linking_id_left linking_id_right.
Qed.

Definition reflection_counit : nat_trans (functor_comp J R) (functor_id G).
Proof.
refine (@Build_nat_trans G G (functor_comp J R) (functor_id G)
  (fun _ => counit_element) _).
move=> x y a; exact: counit_natural.
Defined.

Lemma unit_triangle (X : C) :
    @reflection_map S F L P X B ((@base_arrow S F L P X)) * counit_element = 1.
Proof.
apply: (@distinguished_post_injective S F L (costructured_source X) P ((@base S F L P X))).
rewrite -distinguished_compose -linking_assoc
  (@reflection_triangle S F L P X B (@base_arrow S F L P X)).
change (linking_compose L (linking_compose L ((@base S F L P X)) ((@base S F L P B)))
    (distinguished L counit_element) =
  linking_compose L ((@base S F L P X)) (distinguished L 1)).
by rewrite linking_assoc counit_triangle distinguished_one.
Qed.

Definition subgroup_comparison_adjunction : adjunction R J.
Proof.
refine (@Build_adjunction C G R J (reflection_unit L P) reflection_counit _ _).
- move=> X; exact: unit_triangle.
- move=> x; apply costructured_hom_ext; exact: counit_triangle.
Defined.
End Adjunction.
End DPLinkingCommaAdjunction.

Check DPLinkingCommaAdjunction.subgroup_comparison_adjunction.
Check DPLinkingCommaAdjunction.reflection_counit.
Print Assumptions DPLinkingCommaAdjunction.subgroup_comparison_adjunction.
