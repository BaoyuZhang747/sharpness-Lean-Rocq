(** The native normalizer diagram compares with each actual chain group.
    Compatibility is proved for every actual chain map, not just objects. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory LinkingChainRestrictionMaps LinkingChainRestrictionOperations
  LinkingChainRestrictionUniqueness GroupCohomologyBase GroupCohomologyPullback
  NormalizerOrdinaryCoefficient NormalizerOrdinaryRepresentativeChange.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndex
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations DPLinkingChainRestrictionUniqueness
  DPGroupCohomology DPGroupCohomologyPullback DPNormalizerOrdinaryCoefficient
  DPNormalizerOrdinaryRepresentativeChange.

Module DPNormalizerOrdinaryChainComparison.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation I := (index_category F).
Local Notation M := (@representative_coefficient S F L r hr R A n).

Definition chain_to_representative (c : chain F) : chain_map L c (r (chain_class c)) :=
  equal_class_chain_map L (Logic.eq_sym (hr (chain_class c))).

Definition representative_to_chain (c : chain F) : chain_map L (r (chain_class c)) c :=
  equal_class_chain_map L (hr (chain_class c)).

Definition chain_comparison (c : chain F) : @isomorphism (module_category R)
  (fobj M (chain_class c)) (value R (chain_automorphism_group L c) A n) :=
  chain_cohomology_iso A n (representative_to_chain c) (chain_to_representative c).

Lemma chain_comparison_hom (c : chain F) :
  iso_hom (chain_comparison c) = pull A (restriction_morphism (chain_to_representative c)) n.
Proof. reflexivity. Qed.

Theorem chain_comparison_naturality (c d : chain F) (f : chain_map L c d)
    (u : hom I (chain_class c) (chain_class d)) :
  module_hom_comp (@fmap _ _ M (chain_class d) (chain_class c) u)
    (iso_hom (chain_comparison c)) =
  module_hom_comp (iso_hom (chain_comparison d)) (pull A (restriction_morphism f) n).
Proof.
change (module_hom_comp
  (pull A (restriction_morphism (@arrow_chain_map S F L r hr _ _ u)) n)
  (pull A (restriction_morphism (chain_to_representative c)) n) =
  module_hom_comp (pull A (restriction_morphism (chain_to_representative d)) n)
    (pull A (restriction_morphism f) n)).
rewrite -!pull_composition -!composite_restriction; exact: chain_map_pull_unique.
Qed.
End Comparison.
End DPNormalizerOrdinaryChainComparison.
