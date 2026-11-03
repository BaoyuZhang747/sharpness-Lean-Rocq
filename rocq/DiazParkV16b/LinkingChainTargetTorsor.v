(** Every nonempty actual linking-chain Hom set is a genuine free and
    transitive right action of the compatible target automorphism group. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms LinkingChainRestrictionMaps
  LinkingChainRestrictionUniqueness LinkingChainRestrictionOperations
  LinkingChainTargetAction LinkingChainTargetComparison LinkingChainAutomorphismMaps
  NormalizerLinkingChainExt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionUniqueness DPLinkingChainRestrictionOperations
  DPLinkingChainTargetAction DPLinkingChainTargetComparison DPLinkingChainAutomorphismMaps
  DPNormalizerLinkingChainExt.
Local Open Scope group_scope.

Module DPLinkingChainTargetTorsor.
Section Action.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.

Theorem target_action_transitive (f g : chain_map L c d) :
    target_action f (target_comparison f g) = g.
Proof.
apply (@chain_map_ext S F L c d (target_action f (target_comparison f g)) g
  (selected_indices_unique f g))=> i.
symmetry; exact (target_comparison_property f g i).
Qed.

Theorem target_action_injective (f : chain_map L c d) : injective (target_action f).
Proof.
move=> a b h; apply (@target_action_component_faithful S F L c d f a b)=> i.
exact (@chain_map_eq_same_entry S F L c d (selected_indices f)
  (target_entry_iso f a) (target_entry_iso f b)
  (target_entry_square f a) (target_entry_square f b) h i).
Qed.

Theorem target_action_one (f : chain_map L c d) : target_action f 1 = f.
Proof.
case: f=> e fi hf; apply chain_map_ext_same=> i.
change (linking_compose L (iso_hom (fi i)) (@projection S F L d i 1) = iso_hom (fi i)).
have ho : @projection S F L d i 1 = 1 := @tuple_oneE S F L d i.
rewrite ho automorphism_one linking_id_right; reflexivity.
Qed.

Theorem target_action_multiply (f : chain_map L c d)
    (a b : chain_automorphism_group L d) :
    target_action (target_action f a) b = target_action f (a * b).
Proof.
apply chain_map_ext_same=> i.
change (linking_compose L
  (linking_compose L (iso_hom (entry_isomorphism f i)) (@projection S F L d i a))
  (@projection S F L d i b) =
  linking_compose L (iso_hom (entry_isomorphism f i)) (@projection S F L d i (a * b))).
have hm : @projection S F L d i (a * b) =
  @projection S F L d i a * @projection S F L d i b := tuple_mulE _ _ _.
rewrite hm automorphism_mul linking_assoc; reflexivity.
Qed.
End Action.

Section Endomorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.

Theorem automorphism_chain_map_injective : injective (@automorphism_chain_map S F L c).
Proof. exact (@target_action_injective S F L c c (identity_chain_map L c)). Qed.

Theorem automorphism_chain_map_surjective (f : chain_map L c c) :
    exists a : chain_automorphism_group L c, automorphism_chain_map a = f.
Proof.
exists (target_comparison (identity_chain_map L c) f); exact: target_action_transitive.
Qed.
End Endomorphisms.
End DPLinkingChainTargetTorsor.
