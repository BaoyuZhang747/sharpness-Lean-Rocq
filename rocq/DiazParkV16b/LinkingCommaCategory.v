(** Literal subgroup-comparison comma categories and maps.  At this
    stage no homotopy equivalence or comma-acyclicity is assumed. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryIsomorphism CategoryComma CategoryLeftKan
  FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection GroupCohomologyBase.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingOrbit DPGroupCohomology.
Local Open Scope group_scope.

Module DPLinkingComma.
Section Comma.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition subgroup_comma (P : Obj) : category :=
  costructured_category (orbit_projection L) P.

Definition subgroup_comma_forget (P : Obj) : functor (subgroup_comma P) (linking_category L) :=
  costructured_projection (orbit_projection L) P.

Definition subgroup_comma_map (P Q : Obj)
    (a : hom (DPFusionOrbit.centric_orbit_category F) P Q) :
    functor (subgroup_comma P) (subgroup_comma Q).
Proof.
refine (@Build_functor (subgroup_comma P) (subgroup_comma Q)
  (costructured_reindex_object (orbit_projection L) a)
  (fun X Y u => costructured_reindex_map (orbit_projection L) a u) _ _).
- move=> X; apply costructured_hom_ext; reflexivity.
- move=> X Y Z f g; apply costructured_hom_ext; reflexivity.
Defined.

Lemma subgroup_comma_map_object (P Q : Obj)
    (a : hom (DPFusionOrbit.centric_orbit_category F) P Q) (X : subgroup_comma P) :
    costructured_arrow (fobj (subgroup_comma_map a) X) =
    @compose (DPFusionOrbit.centric_orbit_category F) _ _ _ (costructured_arrow X) a.
Proof. reflexivity. Qed.

Definition distinguished_functor (P : Obj) :
    functor (group_category [subg (val P)]%type) (linking_category L).
Proof.
refine (@Build_functor (group_category [subg (val P)]%type) (linking_category L)
  (fun _ => P) (fun _ _ x => distinguished L x) _ _).
- move=> x; exact: distinguished_one.
- move=> x y z a b; exact: distinguished_mul.
Defined.

Definition subgroup_comparison_object (P : Obj) : subgroup_comma P :=
  @Build_costructured_object (linking_category L) (DPFusionOrbit.centric_orbit_category F)
    (orbit_projection L) P P (@identity (DPFusionOrbit.centric_orbit_category F) P).

Definition subgroup_comparison_arrow (P : Obj) (x : [subg (val P)]) :
    hom (subgroup_comma P) (subgroup_comparison_object P) (subgroup_comparison_object P).
Proof.
refine (@Build_costructured_hom (linking_category L) (DPFusionOrbit.centric_orbit_category F)
  (orbit_projection L) P (subgroup_comparison_object P) (subgroup_comparison_object P)
  (distinguished L x) _).
rewrite compose_id_right; exact: orbit_projection_distinguished.
Defined.

Definition subgroup_comparison (P : Obj) :
    functor (group_category [subg (val P)]%type) (subgroup_comma P).
Proof.
refine (@Build_functor (group_category [subg (val P)]%type) (subgroup_comma P)
  (fun _ => subgroup_comparison_object P) (fun _ _ x => subgroup_comparison_arrow x) _ _).
- move=> x; apply costructured_hom_ext; exact: distinguished_one.
- move=> x y z a b; apply costructured_hom_ext; exact: distinguished_mul.
Defined.

Lemma subgroup_comparison_forget (P : Obj) :
    functor_comp (subgroup_comparison P) (subgroup_comma_forget P) = distinguished_functor P.
Proof.
apply (@functor_extensionality _ _
  (functor_comp (subgroup_comparison P) (subgroup_comma_forget P))
  (distinguished_functor P) Logic.eq_refl); reflexivity.
Qed.

Lemma subgroup_comparison_arrow_map (P : Obj) (x : [subg (val P)]) :
    costructured_map (@fmap _ _ (subgroup_comparison P) tt tt x) = distinguished L x.
Proof. reflexivity. Qed.

Lemma subgroup_comma_map_forget (P Q : Obj)
    (a : hom (DPFusionOrbit.centric_orbit_category F) P Q) :
    functor_comp (subgroup_comma_map a) (subgroup_comma_forget Q) = subgroup_comma_forget P.
Proof.
apply (@functor_extensionality _ _
  (functor_comp (subgroup_comma_map a) (subgroup_comma_forget Q))
  (subgroup_comma_forget P) Logic.eq_refl); reflexivity.
Qed.
End Comma.
End DPLinkingComma.

Check DPLinkingComma.subgroup_comma.
Check DPLinkingComma.subgroup_comparison.
Check DPLinkingComma.subgroup_comparison_forget.
Print Assumptions DPLinkingComma.subgroup_comparison_forget.
Print Assumptions DPLinkingComma.subgroup_comma_map_forget.
