(** Both actual triangle identities for the linking-chain fibre reflection. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryComma CategoryAdjunction FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory LinkingChainRestrictionMaps LinkingChainRestrictionOperations
  LinkingChainTargetAction LinkingChainTargetComparison LinkingChainTargetTorsor
  LinkingChainTargetComposition LinkingChainAutomorphismMaps NormalizerLinkingChainCategory
  NormalizerLinkingChainProjection NormalizerLinkingChainAutomorphismChart
  NormalizerLinkingCommaReflection GroupCohomologyBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndex
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations
  DPLinkingChainTargetAction DPLinkingChainTargetComparison DPLinkingChainTargetTorsor
  DPLinkingChainTargetComposition DPLinkingChainAutomorphismMaps DPNormalizerLinkingChainCategory
  DPNormalizerLinkingChainAutomorphismChart DPNormalizerLinkingCommaReflection DPGroupCohomology.
Local Open Scope group_scope.

Module DPNormalizerLinkingCommaAdjunction.
Section Adjunction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable d : index_category F.
Variable r : chain F.
Hypothesis hr : chain_class r = d.
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).
Local Notation C := (costructured_category P d).
Local Notation G := (group_category (chain_automorphism_group L r)).
Local Notation B := (comparison_object L hr).
Local Notation J := (comparison L hr).
Local Notation R := (reflection L hr).
Local Notation b := (@base S F L d r hr).

Definition counit_element : chain_automorphism_group L r :=
  target_comparison (b B) (identity_chain_map L r).

Lemma counit_action : target_action (b B) counit_element = identity_chain_map L r.
Proof. exact: target_action_transitive. Qed.

Lemma counit_triangle :
    composite_chain_map (b B) (automorphism_chain_map counit_element) = identity_chain_map L r.
Proof. rewrite chain_compose_automorphism; exact: counit_action. Qed.

Lemma counit_natural (a : chain_automorphism_group L r) :
    @reflection_map S F L d r hr B B (@comparison_arrow S F L d r hr a) * counit_element = counit_element * a.
Proof.
apply (@target_action_injective S F L r r (b B)).
rewrite -!target_action_multiply.
rewrite (@reflection_action S F L d r hr B B (@comparison_arrow S F L d r hr a)).
change (target_action (composite_chain_map (automorphism_chain_map a) (b B)) counit_element =
  target_action (target_action (b B) counit_element) a).
rewrite -composite_target_action !counit_action chain_compose_id_right; reflexivity.
Qed.

Definition reflection_counit : nat_trans (functor_comp J R) (functor_id G).
Proof.
refine (@Build_nat_trans G G (functor_comp J R) (functor_id G) (fun _ => counit_element) _).
move=> x y a; exact: counit_natural.
Defined.

Lemma unit_triangle (X : C) :
    @reflection_map S F L d r hr X B (@base_arrow S F L d r hr X) * counit_element = 1.
Proof.
apply (@target_action_injective S F L (costructured_source X) r (b X)).
rewrite -target_action_multiply reflection_action.
change (target_action (composite_chain_map (b X) (b B)) counit_element = target_action (b X) 1).
rewrite -composite_target_action counit_action chain_compose_id_right target_action_one; reflexivity.
Qed.

Definition comparison_adjunction : adjunction R J.
Proof.
refine (@Build_adjunction C G R J (reflection_unit L hr) reflection_counit _ _).
- move=> X; exact: unit_triangle.
- move=> x; apply costructured_hom_ext; exact: counit_triangle.
Defined.
End Adjunction.
End DPNormalizerLinkingCommaAdjunction.
