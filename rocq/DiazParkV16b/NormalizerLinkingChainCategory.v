(** The actual category of nonempty strict centric linking chains, with
    genuine selected-subchain isomorphisms as its morphisms. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainIndices
  LinkingChainRestrictionMaps LinkingChainRestrictionOperations NormalizerLinkingChainExt
  NormalizerLinkingChainComponents.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPNormalizerChainIndices
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations
  DPNormalizerLinkingChainExt DPNormalizerLinkingChainComponents.

Module DPNormalizerLinkingChainCategory.
Section Category.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma chain_compose_id_left (c d : chain F) (f : chain_map L c d) :
  composite_chain_map (identity_chain_map L c) f = f.
Proof.
pose e := selected_indices f.
have hf i : index (selected_indices (composite_chain_map (identity_chain_map L c) f)) i = index e i.
  rewrite compose_index identity_index; reflexivity.
apply (@chain_map_ext_at S F L c d _ f (fun i => index e i) hf (fun i => Logic.eq_refl _))=> i.
rewrite (@composite_entry_at S F L c c d (identity_chain_map L c) f i (index e i) (index e i)
  (Logic.eq_refl _) (@identity_index S F c _) (hf i)).
by rewrite identity_entry_at !entry_at_refl linking_id_left.
Qed.

Lemma chain_compose_id_right (c d : chain F) (f : chain_map L c d) :
  composite_chain_map f (identity_chain_map L d) = f.
Proof.
pose e := selected_indices f.
have hf i : index (selected_indices (composite_chain_map f (identity_chain_map L d))) i = index e i.
  rewrite compose_index identity_index; reflexivity.
apply (@chain_map_ext_at S F L c d _ f (fun i => index e i) hf (fun i => Logic.eq_refl _))=> i.
rewrite (@composite_entry_at S F L c d d f (identity_chain_map L d) i i (index e i)
  (@identity_index S F d i) (Logic.eq_refl _) (hf i)).
by rewrite identity_entry_at !entry_at_refl linking_id_right.
Qed.

Lemma chain_compose_assoc (b c d t : chain F)
    (f : chain_map L b c) (g : chain_map L c d) (h : chain_map L d t) :
  composite_chain_map (composite_chain_map f g) h =
  composite_chain_map f (composite_chain_map g h).
Proof.
pose j i := index (selected_indices f) (index (selected_indices g) (index (selected_indices h) i)).
have hl i : index (selected_indices (composite_chain_map (composite_chain_map f g) h)) i = j i.
  by rewrite !compose_index.
have hr i : index (selected_indices (composite_chain_map f (composite_chain_map g h))) i = j i.
  by rewrite !compose_index.
apply (@chain_map_ext_at S F L b t _ _ j hl hr)=> i.
rewrite (@composite_entry_at S F L b d t (composite_chain_map f g) h i
  (index (selected_indices h) i) (j i) (Logic.eq_refl _)
  (compose_index (selected_indices f) (selected_indices g) _) (hl i)).
rewrite (@composite_entry_at S F L b c t f (composite_chain_map g h) i
  (index (selected_indices g) (index (selected_indices h) i)) (j i)
  (compose_index (selected_indices g) (selected_indices h) i) (Logic.eq_refl _) (hr i)).
rewrite !composite_entry_at_native !entry_at_refl.
exact: linking_assoc.
Qed.

Definition chain_category : category.
Proof.
refine (@Build_category (chain F) (chain_map L) (identity_chain_map L)
  (@composite_chain_map S F L) _ _ _).
- intros; exact: chain_compose_id_left.
- intros; exact: chain_compose_id_right.
- intros; exact: chain_compose_assoc.
Defined.

Lemma chain_category_identity (c : chain F) :
  @Category.identity chain_category c = identity_chain_map L c.
Proof. reflexivity. Qed.

Lemma chain_category_compose (b c d : chain F) (f : chain_map L b c) (g : chain_map L c d) :
  @Category.compose chain_category b c d f g = composite_chain_map f g.
Proof. reflexivity. Qed.

End Category.
End DPNormalizerLinkingChainCategory.
