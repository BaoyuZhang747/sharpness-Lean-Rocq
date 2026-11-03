(** Changing representatives of normalizer classes gives the genuine
    natural isomorphism induced by compatible linking-chain maps. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryNaturalIso
  FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainRelations NormalizerChainIndexCategory LinkingChainRestrictionMaps
  LinkingChainRestrictionUniqueness LinkingChainRestrictionOperations LinkingChainWitnessLift
  GroupCohomologyBase GroupCohomologyPullback NormalizerOrdinaryCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainRelations DPNormalizerChainIndex DPLinkingChainRestrictionMaps
  DPLinkingChainRestrictionUniqueness DPLinkingChainRestrictionOperations DPLinkingChainWitnessLift
  DPGroupCohomology DPGroupCohomologyPullback DPNormalizerOrdinaryCoefficient.

Module DPNormalizerOrdinaryRepresentativeChange.
Section Maps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma equal_class_witness_exists (c d : chain F) (h : chain_class c = chain_class d) :
  exists a : chain_witness c d, True.
Proof.
have hr : index_relation (chain_class c) (chain_class d).
  rewrite h; exact: index_relation_refl.
rewrite class_relation in hr; have /subconjugateP [a] := hr.
exists a; exact Logic.I.
Qed.

Definition equal_class_chain_map (c d : chain F) (h : chain_class c = chain_class d) : chain_map L c d :=
  witness_chain_map L (proj1_sig (cid (equal_class_witness_exists h))).

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Definition chain_cohomology_iso (c d : chain F) (f : chain_map L c d) (g : chain_map L d c) :
  @isomorphism (module_category R) (value R (chain_automorphism_group L c) A n)
    (value R (chain_automorphism_group L d) A n).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (pull A (restriction_morphism g) n) (pull A (restriction_morphism f) n) _ _).
- change (module_hom_comp (pull A (restriction_morphism g) n)
    (pull A (restriction_morphism f) n) = module_hom_id _).
  rewrite -pull_composition -composite_restriction.
  rewrite (@chain_map_pull_unique S F L c c (composite_chain_map f g)
    (identity_chain_map L c) R A n) identity_restriction pull_identity; reflexivity.
- change (module_hom_comp (pull A (restriction_morphism f) n)
    (pull A (restriction_morphism g) n) = module_hom_id _).
  rewrite -pull_composition -composite_restriction.
  rewrite (@chain_map_pull_unique S F L d d (composite_chain_map g f)
    (identity_chain_map L d) R A n) identity_restriction pull_identity; reflexivity.
Defined.

Variables r s : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Hypothesis hs : forall d, chain_class (s d) = d.
Local Notation I := (index_category F).
Local Notation D := (@representative_coefficient S F L r hr R A n).
Local Notation E := (@representative_coefficient S F L s hs R A n).

Definition forward_chain_map d : chain_map L (r d) (s d) :=
  equal_class_chain_map (Logic.eq_trans (hr d) (Logic.eq_sym (hs d))).
Definition backward_chain_map d : chain_map L (s d) (r d) :=
  equal_class_chain_map (Logic.eq_trans (hs d) (Logic.eq_sym (hr d))).

Definition representative_comparison_component d : @isomorphism (module_category R)
  (fobj D d) (fobj E d) := chain_cohomology_iso (forward_chain_map d) (backward_chain_map d).

Lemma representative_comparison_naturality (d e : I) (u : hom I d e) :
  module_hom_comp (@fmap _ _ D e d u) (iso_hom (representative_comparison_component d)) =
    module_hom_comp (iso_hom (representative_comparison_component e)) (@fmap _ _ E e d u).
Proof.
change (module_hom_comp (pull A (restriction_morphism (@arrow_chain_map S F L r hr d e u)) n)
  (pull A (restriction_morphism (backward_chain_map d)) n) =
  module_hom_comp (pull A (restriction_morphism (backward_chain_map e)) n)
  (pull A (restriction_morphism (@arrow_chain_map S F L s hs d e u)) n)).
rewrite -!pull_composition -!composite_restriction.
exact: chain_map_pull_unique.
Qed.

Definition representative_coefficient_iso :
  @isomorphism (functor_category (opposite I) (module_category R)) D E.
Proof.
apply (@nat_iso_of_components _ _ D E representative_comparison_component).
move=> d e u; exact: representative_comparison_naturality.
Defined.

Theorem representative_coefficient_iso_hom d :
  component (iso_hom representative_coefficient_iso) d =
  pull A (restriction_morphism (backward_chain_map d)) n.
Proof. reflexivity. Qed.
End Maps.
End DPNormalizerOrdinaryRepresentativeChange.
