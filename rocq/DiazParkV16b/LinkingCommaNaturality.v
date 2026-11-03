(** The actual linking arrow gives the naturality transformation of
    subgroup comparisons, including noninvertible linking arrows. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection LinkingCommaCategory
  LinkingCommaAdjunction GroupCohomologyBase GroupCohomologyFunctor.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingOrbit DPLinkingComma DPGroupCohomology DPGroupCohomologyFunctor.
Local Open Scope group_scope.

Module DPLinkingCommaNaturality.
Section Naturality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition arrow_group_hom (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
    {morphism [set: [subg P]] >-> [subg Q]}.
Proof.
apply: (Morphism (mfun := arrow_element a)).
move=> x y _ _; apply val_inj; exact: DPFusion.map_mul (valP x) (valP y).
Defined.

Lemma arrow_group_hom_apply (P Q : {group S}) (a : DPFusionSystem.arrow F P Q)
    (x : [subg P]) : arrow_group_hom a x = arrow_element a x.
Proof. reflexivity. Qed.

Definition comparison_naturality_component (P Q : Obj) (f : linking_hom L P Q) :
    hom (subgroup_comma L Q)
      (fobj (subgroup_comma_map L (fmap (orbit_projection L) f)) (subgroup_comparison_object L P))
      (subgroup_comparison_object L Q).
Proof.
refine (@Build_costructured_hom (linking_category L) (DPFusionOrbit.centric_orbit_category F)
  (orbit_projection L) Q
  (fobj (subgroup_comma_map L (fmap (orbit_projection L) f)) (subgroup_comparison_object L P))
  (subgroup_comparison_object L Q) f _).
change (@compose (DPFusionOrbit.centric_orbit_category F) P Q Q
    (fmap (orbit_projection L) f) (@identity (DPFusionOrbit.centric_orbit_category F) Q) =
  @compose (DPFusionOrbit.centric_orbit_category F) P P Q
    (@identity (DPFusionOrbit.centric_orbit_category F) P) (fmap (orbit_projection L) f)).
by rewrite compose_id_left compose_id_right.
Defined.

Definition comparison_naturality (P Q : Obj) (f : linking_hom L P Q) :
    nat_trans
      (functor_comp (subgroup_comparison L P)
        (subgroup_comma_map L (fmap (orbit_projection L) f)))
      (functor_comp (group_functor (arrow_group_hom (linking_projection L f)))
        (subgroup_comparison L Q)).
Proof.
refine (@Build_nat_trans (group_category [subg (val P)]%type) (subgroup_comma L Q)
  (functor_comp (subgroup_comparison L P) (subgroup_comma_map L (fmap (orbit_projection L) f)))
  (functor_comp (group_functor (arrow_group_hom (linking_projection L f))) (subgroup_comparison L Q))
  (fun _ => comparison_naturality_component f) _).
move=> x y g; apply costructured_hom_ext; exact: commutation.
Defined.

Lemma comparison_naturality_component_map (P Q : Obj) (f : linking_hom L P Q) :
    costructured_map (component (comparison_naturality f) tt) = f.
Proof. reflexivity. Qed.
End Naturality.
End DPLinkingCommaNaturality.

Check DPLinkingCommaNaturality.comparison_naturality.
Check DPLinkingCommaNaturality.comparison_naturality_component_map.
Print Assumptions DPLinkingCommaNaturality.comparison_naturality.
Print Assumptions DPLinkingCommaNaturality.comparison_naturality_component_map.
