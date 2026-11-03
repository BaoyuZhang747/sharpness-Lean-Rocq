(** Actual group-category maps into BLO's enlarged linking categories.
    Every natural transformation below is induced by a linking morphism. *)
From mathcomp Require Import all_boot all_algebra all_fingroup center boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryModules
  FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemTransporter
  LinkingCommaCategory LinkingCommaNaturality GroupCohomologyBase
  GroupCohomologyFunctor GroupCohomologyPullback CategoryConstantCohomology.
From DiazParkBLO Require Import BLODiagram.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPBLODiagram DPGroupCohomology DPGroupCohomologyFunctor.
Local Open Scope group_scope.

Module DPBLOCohomologyDistinguished.
Section Distinguished.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable E : {group S}.

Definition distinguished_arrow (X : enlarged_object F E)
    (g : [subg (val (underlying X))]) :
    hom (enlarged_category L E) X X.
Proof.
refine (@Arrow S F L E X X (DPCentricLinking.distinguished L g) _).
apply DPFusionSystem.arrow_ext=> x Ex.
rewrite DPFusion.compose_in // !alpha_to_carrierE //.
rewrite /DPCentricLinking.distinguished DPCentricLinking.projection_transporter /=.
have hxZ := DPFusion.map_into (val (alpha X)) Ex.
have hxP := subsetP (center_sub (val (underlying X))) _ hxZ.
rewrite DPFusion.conjugation_in //.
apply/conjg_fixP/commgP.
exact: (centP (setIP hxZ).2 (val g) (valP g)).
Defined.

Definition distinguished_functor (X : enlarged_object F E) :
    functor (group_category [subg (val (underlying X))]%type)
      (enlarged_category L E).
Proof.
refine (@Build_functor (group_category [subg (val (underlying X))]%type)
  (enlarged_category L E) (fun _ => X)
  (fun _ _ g => @distinguished_arrow X g) _ _).
- move=> x; apply enlarged_hom_ext; exact: DPCentricLinking.distinguished_one.
- move=> x y z g h; apply enlarged_hom_ext; exact: DPCentricLinking.distinguished_mul.
Defined.

Lemma distinguished_forgetful (X : enlarged_object F E) :
    functor_comp (distinguished_functor X) (forgetful L E) =
      DPLinkingComma.distinguished_functor L (underlying X).
Proof.
apply (@CategoryIsomorphism.functor_extensionality
  (group_category [subg (val (underlying X))]%type) (DPCentricLinking.linking_category L)
  (functor_comp (distinguished_functor X) (forgetful L E))
  (DPLinkingComma.distinguished_functor L (underlying X)) (Logic.eq_refl _)); reflexivity.
Qed.

Definition linking_naturality (X Y : enlarged_object F E)
    (f : hom (enlarged_category L E) X Y) :
    nat_trans (distinguished_functor X)
      (functor_comp
        (group_functor (DPLinkingCommaNaturality.arrow_group_hom
          (DPCentricLinking.linking_projection L (underlying_hom f))))
        (distinguished_functor Y)).
Proof.
refine (@Build_nat_trans (group_category [subg (val (underlying X))]%type)
  (enlarged_category L E) (distinguished_functor X)
  (functor_comp
    (group_functor (DPLinkingCommaNaturality.arrow_group_hom
      (DPCentricLinking.linking_projection L (underlying_hom f))))
    (distinguished_functor Y)) (fun _ => f) _).
move=> x y g; apply enlarged_hom_ext; exact: DPCentricLinking.commutation.
Defined.

Lemma linking_pull_naturality (R : comPzRingType) (A : lmodType R)
    (X Y : enlarged_object F E) (f : hom (enlarged_category L E) X Y) n :
    DPCategoryConstantCohomology.pull A (distinguished_functor X) n =
    module_hom_comp (DPCategoryConstantCohomology.pull A (distinguished_functor Y) n)
      (DPGroupCohomologyPullback.pull A
        (DPLinkingCommaNaturality.arrow_group_hom
          (DPCentricLinking.linking_projection L (underlying_hom f))) n).
Proof.
change (DPCategoryConstantCohomology.pull A (distinguished_functor X) n =
  module_hom_comp (DPCategoryConstantCohomology.pull A (distinguished_functor Y) n)
    (DPCategoryConstantCohomology.pull A
      (group_functor (DPLinkingCommaNaturality.arrow_group_hom
        (DPCentricLinking.linking_projection L (underlying_hom f)))) n)).
rewrite -DPCategoryConstantCohomology.pull_composition.
symmetry; exact (@DPCategoryConstantCohomology.pull_nat_trans R A _ _ _ _
  (linking_naturality f) n).
Qed.
End Distinguished.

Section Precomposition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables E E' : {group S}.
Variable u : DPFusionSystem.arrow F E E'.

Lemma distinguished_precompose (X : enlarged_object F E') :
    functor_comp (distinguished_functor L X) (precompose L u) =
      distinguished_functor L (precompose_object u X).
Proof.
apply (@CategoryIsomorphism.functor_extensionality
  (group_category [subg (val (underlying X))]%type) (enlarged_category L E)
  (functor_comp (distinguished_functor L X) (precompose L u))
  (distinguished_functor L (precompose_object u X)) (Logic.eq_refl _)).
apply functional_extensionality_dep=> x; apply functional_extensionality_dep=> y.
apply functional_extensionality_dep=> g; apply enlarged_hom_ext; reflexivity.
Qed.
End Precomposition.
End DPBLOCohomologyDistinguished.
