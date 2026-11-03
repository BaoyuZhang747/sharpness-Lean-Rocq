(** Actual fibre cohomology is naturally the explicit native ChainAut
    coefficient on the same normalizer index. Every comparison is pullback
    along the constructed one-object chart; every arrow is literal restriction. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryComma CategoryModules CategoryExtensionality
  CategoryNaturalIso CategoryDerivedLimits FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory LinkingChainRestrictionMaps NormalizerLinkingChainCategory
  NormalizerLinkingChainProjection NormalizerLinkingChainAutomorphismChart
  NormalizerLinkingCommaReflection NormalizerLinkingCommaAdjunction NormalizerLinkingCommaNaturality
  CategoryCostructuredDiagram CategoryConstantCohomology CategoryCostructuredCohomologyDiagram
  GroupCohomologyBase GroupCohomologyFunctor GroupCohomologyPullback NormalizerOrdinaryCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndex
  DPLinkingChainRestrictionMaps DPNormalizerLinkingChainCategory
  DPNormalizerLinkingChainAutomorphismChart DPNormalizerLinkingCommaReflection
  DPNormalizerLinkingCommaAdjunction DPCategoryCostructuredDiagram.

Module DPNormalizerLinkingCommaCohomology.
Section Cohomology.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variable n : nat.
Local Notation I := (index_category F).
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).
Local Notation CC := (@DPCategoryCostructuredCohomologyDiagram.coefficient R A (chain_category L) I P n).
Local Notation NC := (@DPNormalizerOrdinaryCoefficient.representative_coefficient S F L r hr R A n).

Definition comparison_iso (d : I) : @isomorphism (module_category R)
    (fobj CC d) (DPGroupCohomology.value R (chain_automorphism_group L (r d)) A n) :=
  DPCategoryConstantCohomology.adjunction_iso A (@comparison_adjunction S F L d (r d) (hr d)) n.

Lemma comparison_iso_hom (d : I) :
    iso_hom (comparison_iso d) =
    DPCategoryConstantCohomology.pull A (@comparison S F L d (r d) (hr d)) n.
Proof. reflexivity. Qed.

Lemma comparison_iso_inv (d : I) :
    iso_inv (comparison_iso d) =
    DPCategoryConstantCohomology.pull A (@reflection S F L d (r d) (hr d)) n.
Proof. reflexivity. Qed.

Theorem comparison_naturality (d e : I) (u : hom I d e) (f : chain_map L (r d) (r e)) :
    module_hom_comp (@fmap _ _ CC e d u) (iso_hom (comparison_iso d)) =
    module_hom_comp (iso_hom (comparison_iso e))
      (DPGroupCohomologyPullback.pull A (restriction_morphism f) n).
Proof.
change (module_hom_comp (DPCategoryConstantCohomology.pull A (reindex P u) n)
  (DPCategoryConstantCohomology.pull A (@comparison S F L d (r d) (hr d)) n) =
  module_hom_comp (DPCategoryConstantCohomology.pull A (@comparison S F L e (r e) (hr e)) n)
  (DPCategoryConstantCohomology.pull A
    (DPGroupCohomologyFunctor.group_functor (restriction_morphism f)) n)).
rewrite -!DPCategoryConstantCohomology.pull_composition.
symmetry; exact (@DPCategoryConstantCohomology.pull_nat_trans R A _ _ _ _
  (@DPNormalizerLinkingCommaNaturality.comparison_transformation S F L d e
    (r d) (r e) (hr d) (hr e) u f) n).
Qed.

Definition comparison_nat_iso :
    @isomorphism (functor_category (opposite I) (module_category R)) CC NC.
Proof.
refine (@nat_iso_of_components (opposite I) (module_category R) CC NC comparison_iso _).
move=> d e u.
rewrite (@DPNormalizerOrdinaryCoefficient.representative_coefficient_map S F L r hr R A n
  e d u (@DPNormalizerOrdinaryCoefficient.arrow_chain_map S F L r hr e d u)).
exact: comparison_naturality.
Defined.

Lemma comparison_nat_iso_hom (d : I) :
    component (iso_hom comparison_nat_iso) d =
    DPCategoryConstantCohomology.pull A (@comparison S F L d (r d) (hr d)) n.
Proof. reflexivity. Qed.

Lemma comparison_nat_iso_inv (d : I) :
    component (iso_inv comparison_nat_iso) d =
    DPCategoryConstantCohomology.pull A (@reflection S F L d (r d) (hr d)) n.
Proof. reflexivity. Qed.

Theorem comparison_forget (d : I) :
    module_hom_comp (DPCategoryConstantCohomology.pull A (costructured_projection P d) n)
      (iso_hom (comparison_iso d)) =
    DPCategoryConstantCohomology.pull A (automorphism_chart L (r d)) n.
Proof.
rewrite comparison_iso_hom -DPCategoryConstantCohomology.pull_composition
  DPNormalizerLinkingCommaNaturality.comparison_forget; reflexivity.
Qed.

Definition higher_limit_iso (j : nat) : @isomorphism (module_category R)
    (derived_limit R CC j) (derived_limit R NC j) :=
  functor_iso (derived_limit_functor R (opposite I) j) comparison_nat_iso.

Lemma higher_limit_iso_hom (j : nat) :
    iso_hom (higher_limit_iso j) = derived_limit_map R (iso_hom comparison_nat_iso) j.
Proof. reflexivity. Qed.
End Cohomology.

Definition canonical_comparison_nat_iso (R : comPzRingType) (A : lmodType R)
    (S : finGroupType) (F : DPFusionSystem.system S) (L : DPCentricLinking.system F) (n : nat) :
    @isomorphism (functor_category (opposite (index_category F)) (module_category R))
      (@DPCategoryCostructuredCohomologyDiagram.coefficient R A (chain_category L)
        (index_category F) (DPNormalizerLinkingChainProjection.projection L) n)
      (@DPNormalizerOrdinaryCoefficient.coefficient S F L R A n) :=
  @comparison_nat_iso R A S F L (@DPNormalizerOrdinaryCoefficient.canonical_representative S F)
    (@DPNormalizerOrdinaryCoefficient.canonical_representative_class S F) n.
End DPNormalizerLinkingCommaCohomology.
