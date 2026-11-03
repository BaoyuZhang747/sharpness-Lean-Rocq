(** Genuine naturality of the ChainAut comparison charts over every
    actual normalizer-index arrow and every linking-chain map above it. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryComma CategoryIsomorphism FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory LinkingChainRestrictionMaps NormalizerLinkingChainCategory
  NormalizerLinkingChainProjection NormalizerLinkingChainAutomorphismChart
  NormalizerLinkingCommaReflection CategoryCostructuredDiagram
  GroupCohomologyBase GroupCohomologyFunctor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndex
  DPLinkingChainRestrictionMaps DPNormalizerLinkingChainCategory
  DPNormalizerLinkingChainAutomorphismChart DPNormalizerLinkingCommaReflection
  DPCategoryCostructuredDiagram DPGroupCohomology DPGroupCohomologyFunctor.

Module DPNormalizerLinkingCommaNaturality.
Section Naturality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).
Variables d e : index_category F.
Variables r s : chain F.
Hypotheses (hr : chain_class r = d) (hs : chain_class s = e).
Variable u : hom (index_category F) d e.
Variable f : chain_map L r s.
Local Notation Jd := (comparison L hr).
Local Notation Je := (comparison L hs).
Local Notation G := (group_category (chain_automorphism_group L r)).
Local Notation E := (costructured_category P e).

Definition comparison_component (x : G) :
    hom E (fobj (functor_comp Jd (reindex P u)) x)
      (fobj (functor_comp (group_functor (restriction_morphism f)) Je) x).
Proof.
refine (@Build_costructured_hom (chain_category L) (index_category F) P e
  (fobj (functor_comp Jd (reindex P u)) x)
  (fobj (functor_comp (group_functor (restriction_morphism f)) Je) x) f _).
exact: index_hom_unique.
Defined.

Definition comparison_transformation :
    nat_trans (functor_comp Jd (reindex P u))
      (functor_comp (group_functor (restriction_morphism f)) Je).
Proof.
refine (@Build_nat_trans G E (functor_comp Jd (reindex P u))
  (functor_comp (group_functor (restriction_morphism f)) Je) comparison_component _).
move=> x y a; apply costructured_hom_ext.
exact (@naturality _ _ _ _ (restriction_chart_transformation f) x y a).
Defined.

Lemma comparison_transformation_map (x : G) :
    costructured_map (component comparison_transformation x) = f.
Proof. reflexivity. Qed.
End Naturality.

Section Forget.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable d : index_category F.
Variable r : chain F.
Hypothesis hr : chain_class r = d.
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).

Theorem comparison_forget :
    functor_comp (comparison L hr) (costructured_projection P d) = automorphism_chart L r.
Proof.
apply (@functor_extensionality _ _
  (functor_comp (comparison L hr) (costructured_projection P d)) (automorphism_chart L r)
  Logic.eq_refl); reflexivity.
Qed.
End Forget.
End DPNormalizerLinkingCommaNaturality.
