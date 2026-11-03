(** Actual constant-bar cohomology of the linking comma category is
    naturally the native group cohomology of P.  All maps are literal
    functor pullbacks; the proof uses the constructed prism homotopy. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection LinkingCommaCategory
  LinkingCommaReflection LinkingCommaAdjunction LinkingCommaNaturality CategoryConstantCohomology
  GroupCohomologyBase GroupCohomologyFunctor GroupCohomologyPullback.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingOrbit DPLinkingComma DPLinkingCommaReflection
  DPLinkingCommaAdjunction DPLinkingCommaNaturality.
Local Open Scope group_scope.

Module DPLinkingCommaCohomology.
Section Cohomology.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition value (P : Obj) n : lmodType R :=
  DPCategoryConstantCohomology.value R A (subgroup_comma L P) n.

Definition pull (P Q : Obj) (a : hom (DPFusionOrbit.centric_orbit_category F) P Q) n :
    module_hom (value Q n) (value P n) :=
  DPCategoryConstantCohomology.pull A (subgroup_comma_map L a) n.

Definition comparison_iso (P : Obj) n : @isomorphism (module_category R)
    (value P n) (DPGroupCohomology.value R [subg (val P)]%type A n) :=
  DPCategoryConstantCohomology.adjunction_iso A (subgroup_comparison_adjunction L P) n.

Lemma comparison_iso_hom (P : Obj) n :
    iso_hom (comparison_iso P n) =
    DPCategoryConstantCohomology.pull A (subgroup_comparison L P) n.
Proof. reflexivity. Qed.

Lemma comparison_iso_inv (P : Obj) n :
    iso_inv (comparison_iso P n) =
    DPCategoryConstantCohomology.pull A (reflection L P) n.
Proof. reflexivity. Qed.

Theorem comparison_naturality (P Q : Obj) (f : linking_hom L P Q) n :
    module_hom_comp (pull (fmap (orbit_projection L) f) n) (iso_hom (comparison_iso P n)) =
    module_hom_comp (iso_hom (comparison_iso Q n))
      (DPGroupCohomologyPullback.pull A (arrow_group_hom (linking_projection L f)) n).
Proof.
change (module_hom_comp
  (DPCategoryConstantCohomology.pull A (subgroup_comma_map L (fmap (orbit_projection L) f)) n)
  (DPCategoryConstantCohomology.pull A (subgroup_comparison L P) n) =
  module_hom_comp (DPCategoryConstantCohomology.pull A (subgroup_comparison L Q) n)
  (DPCategoryConstantCohomology.pull A
    (DPGroupCohomologyFunctor.group_functor (arrow_group_hom (linking_projection L f))) n)).
rewrite -!DPCategoryConstantCohomology.pull_composition.
symmetry; exact (@DPCategoryConstantCohomology.pull_nat_trans R A _ _ _ _
  (DPLinkingCommaNaturality.comparison_naturality f) n).
Qed.

Theorem comparison_forget (P : Obj) n :
    module_hom_comp
      (DPCategoryConstantCohomology.pull A (subgroup_comma_forget L P) n)
      (iso_hom (comparison_iso P n)) =
    DPCategoryConstantCohomology.pull A (distinguished_functor L P) n.
Proof.
rewrite comparison_iso_hom -DPCategoryConstantCohomology.pull_composition subgroup_comparison_forget.
reflexivity.
Qed.
End Cohomology.
End DPLinkingCommaCohomology.

Check DPLinkingCommaCohomology.comparison_iso.
Check DPLinkingCommaCohomology.comparison_naturality.
Check DPLinkingCommaCohomology.comparison_forget.
Print Assumptions DPLinkingCommaCohomology.comparison_iso.
Print Assumptions DPLinkingCommaCohomology.comparison_naturality.
Print Assumptions DPLinkingCommaCohomology.comparison_forget.
