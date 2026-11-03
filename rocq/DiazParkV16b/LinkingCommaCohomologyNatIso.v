(** A genuine natural isomorphism between the actual comma cohomology
    diagram and the native group-cohomology orbit coefficient functor. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules CategoryExtensionality
  CategoryNaturalIso CategoryDerivedLimits FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection LinkingCommaCategory
  LinkingCommaNaturality LinkingCommaReflection CategoryConstantCohomology
  LinkingCommaCohomology LinkingCommaCohomologyDiagram
  GroupCohomologyOrbitCoefficient.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingOrbit.

Module DPLinkingCommaCohomologyNatIso.
Section Comparison.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable n : nat.
Local Notation O := (DPFusionOrbit.centric_orbit_category F).
Local Notation CC := (DPLinkingCommaCohomologyDiagram.coefficient L A n).
Local Notation GC := (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n).

Lemma comparison_orbit_naturality (P Q : O) (a : hom O P Q) :
    module_hom_comp (@fmap _ _ CC Q P a)
      (iso_hom (DPLinkingCommaCohomology.comparison_iso A L P n)) =
    module_hom_comp (iso_hom (DPLinkingCommaCohomology.comparison_iso A L Q n))
      (@fmap _ _ GC Q P a).
Proof.
pose f := lift_orbit_arrow L a.
have ha : fmap (orbit_projection L) f = a := orbit_projection_lift L a.
rewrite -ha !orbit_projection_map DPGroupCohomologyOrbitCoefficient.centric_coefficient_map.
exact: DPLinkingCommaCohomology.comparison_naturality.
Qed.

Definition comparison_nat_iso :
    @isomorphism (functor_category (opposite O) (module_category R)) CC GC.
Proof.
refine (@nat_iso_of_components (opposite O) (module_category R) CC GC
  (fun P => DPLinkingCommaCohomology.comparison_iso A L P n) _).
move=> P Q a; exact: comparison_orbit_naturality.
Defined.

Lemma comparison_nat_iso_hom (P : O) :
    component (iso_hom comparison_nat_iso) P =
    DPCategoryConstantCohomology.pull A (DPLinkingComma.subgroup_comparison L P) n.
Proof. reflexivity. Qed.

Lemma comparison_nat_iso_inv (P : O) :
    component (iso_inv comparison_nat_iso) P =
    DPCategoryConstantCohomology.pull A (DPLinkingCommaReflection.reflection L P) n.
Proof. reflexivity. Qed.

Definition higher_limit_iso (i : nat) : @isomorphism (module_category R)
    (derived_limit R CC i) (derived_limit R GC i) :=
  functor_iso (derived_limit_functor R (opposite O) i) comparison_nat_iso.

Lemma higher_limit_iso_hom (i : nat) :
    iso_hom (higher_limit_iso i) = derived_limit_map R (iso_hom comparison_nat_iso) i.
Proof. reflexivity. Qed.
End Comparison.
End DPLinkingCommaCohomologyNatIso.

Check DPLinkingCommaCohomologyNatIso.comparison_nat_iso.
Check DPLinkingCommaCohomologyNatIso.higher_limit_iso.
Print Assumptions DPLinkingCommaCohomologyNatIso.comparison_nat_iso.
Print Assumptions DPLinkingCommaCohomologyNatIso.higher_limit_iso.
Print Assumptions DPLinkingCommaCohomologyNatIso.higher_limit_iso_hom.
