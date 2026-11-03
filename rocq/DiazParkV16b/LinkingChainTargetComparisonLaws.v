(** Coherence of the constructed target-comparison element follows from
    the actual free action, including precomposition by a chain map. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  LinkingChainRestrictionMaps LinkingChainRestrictionOperations LinkingChainTargetAction
  LinkingChainTargetComparison LinkingChainTargetTorsor LinkingChainTargetComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPLinkingChainAutomorphisms DPLinkingChainRestrictionMaps
  DPLinkingChainRestrictionOperations DPLinkingChainTargetAction DPLinkingChainTargetComparison
  DPLinkingChainTargetTorsor DPLinkingChainTargetComposition.
Local Open Scope group_scope.

Module DPLinkingChainTargetComparisonLaws.
Section Laws.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.

Theorem target_comparison_identity (f : chain_map L c d) : target_comparison f f = 1.
Proof.
apply (@target_action_injective S F L c d f).
rewrite target_action_transitive target_action_one; reflexivity.
Qed.

Theorem target_comparison_cocycle (f g h : chain_map L c d) :
    target_comparison f h = target_comparison f g * target_comparison g h.
Proof.
apply (@target_action_injective S F L c d f).
rewrite -target_action_multiply !target_action_transitive; reflexivity.
Qed.
End Laws.

Section Precomposition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d t : chain F.
Variable f : chain_map L c d.
Variables g h : chain_map L d t.

Theorem target_comparison_precompose :
    target_comparison (composite_chain_map f g) (composite_chain_map f h) = target_comparison g h.
Proof.
apply (@target_action_injective S F L c t (composite_chain_map f g)).
rewrite target_action_transitive -composite_target_action target_action_transitive; reflexivity.
Qed.
End Precomposition.
End DPLinkingChainTargetComparisonLaws.
