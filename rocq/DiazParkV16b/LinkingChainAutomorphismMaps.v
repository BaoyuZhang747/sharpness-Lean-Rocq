(** Compatible automorphism tuples give actual endomorphisms of the
    linking-chain category, and induce precisely inner group conjugation. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryAdjointUniqueness FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  CategoryAutomorphismConjugation LinkingChainRestrictionMaps LinkingChainTransportEqualities
  LinkingChainRestrictionOperations LinkingChainTargetAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps DPLinkingChainTransportEqualities
  DPLinkingChainRestrictionOperations DPLinkingChainTargetAction DPCategoryAutomorphismConjugation.
Local Open Scope group_scope.

Module DPLinkingChainAutomorphismMaps.
Section Maps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation G := (chain_automorphism_group L c).

Definition automorphism_chain_map (a : G) : chain_map L c c :=
  target_action (identity_chain_map L c) a.

Lemma automorphism_chain_map_selection (a : G) :
    selected_indices (automorphism_chain_map a) = DPNormalizerChainIndices.identity c.
Proof. reflexivity. Qed.

Lemma automorphism_chain_map_component (a : G) (i : 'I_(length c).+1) :
    iso_hom (entry_isomorphism (automorphism_chain_map a) i) =
    linking_compose L (iso_hom (@entry_equality_iso S F L c _ _ (@identity_index S F c i)))
      (@projection S F L c i a).
Proof. reflexivity. Qed.

Theorem automorphism_chain_map_restriction (a x : G) :
    restriction_morphism (automorphism_chain_map a) x = a^-1 * x * a.
Proof.
apply projection_ext=> i.
rewrite restriction_morphism_component.
change (conjugate (isomorphism_composition
  (@entry_equality_iso S F L c _ _ (@identity_index S F c i))
  (automorphism_isomorphism (@projection S F L c i a)))
  (@projection S F L c (index (DPNormalizerChainIndices.identity c) i) x) =
  @projection S F L c i (a^-1 * x * a)).
rewrite conjugate_iso_composition projection_conjugate_equality.
have hm (u v : G) : @projection S F L c i (u * v) =
    @projection S F L c i u * @projection S F L c i v := tuple_mulE _ _ _.
have hi : @projection S F L c i a^-1 = (@projection S F L c i a)^-1 := tuple_invE _ _.
rewrite !hm hi.
rewrite /conjugate /automorphism_isomorphism !automorphism_mul linking_assoc; reflexivity.
Qed.
End Maps.
End DPLinkingChainAutomorphismMaps.
