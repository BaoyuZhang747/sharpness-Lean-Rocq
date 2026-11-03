(** Literal evaluation at the first subgroup of an actual linking chain. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices LinkingChainRestrictionMaps LinkingChainRestrictionOperations
  LinkingChainTransportEqualities NormalizerLinkingChainCategory.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndices
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations
  DPLinkingChainTransportEqualities DPNormalizerLinkingChainCategory.

Module DPNormalizerLinkingChainEvaluation.
Section Evaluation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Definition bottom_inclusion (c : chain F) (i : 'I_(length c).+1) :
  linking_hom L (entry c ord0) (entry c i) :=
  @chain_inclusion S F L c ord0 i (leq0n i).
Arguments bottom_inclusion c i : clear implicits.

Lemma bottom_inclusion_refl (c : chain F) :
  bottom_inclusion c ord0 = linking_identity L (entry c ord0).
Proof.
have hp : leq0n (val (ord0 : 'I_(length c).+1)) = leqnn (ord0 : 'I_(length c).+1) :=
  Prop_irrelevance _ _.
rewrite /bottom_inclusion hp; exact: chain_inclusion_refl.
Qed.

Lemma bottom_inclusion_compose (c : chain F) (i j : 'I_(length c).+1) (hij : i <= j) :
  linking_compose L (bottom_inclusion c i) (@chain_inclusion S F L c i j hij) =
  bottom_inclusion c j.
Proof.
rewrite /bottom_inclusion chain_inclusion_compose.
have -> : leq_trans (leq0n i) hij = leq0n j := Prop_irrelevance _ _; reflexivity.
Qed.

Lemma bottom_inclusion_chart (c : chain F) (i j : 'I_(length c).+1) (h : i = j) :
  linking_compose L (bottom_inclusion c i)
    (iso_hom (@entry_equality_iso S F L c i j h)) = bottom_inclusion c j.
Proof. case: j / h; exact: linking_id_right. Qed.

Definition bottom_arrow (c d : chain F) (f : chain_map L c d) (i : 'I_(length d).+1) :
  linking_hom L (entry c ord0) (entry d i) :=
  linking_compose L (bottom_inclusion c (index (selected_indices f) i))
    (iso_hom (entry_isomorphism f i)).

Lemma bottom_arrow_square (c d : chain F) (f : chain_map L c d)
    (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (bottom_arrow f i) (@chain_inclusion S F L d i j hij) = bottom_arrow f j.
Proof.
rewrite /bottom_arrow linking_assoc -(entry_square f hij) -linking_assoc bottom_inclusion_compose.
reflexivity.
Qed.

Lemma bottom_arrow_composite (c d t : chain F) (f : chain_map L c d) (g : chain_map L d t)
    (i : 'I_(length t).+1) :
  bottom_arrow (composite_chain_map f g) i =
  linking_compose L (bottom_arrow f (index (selected_indices g) i))
    (iso_hom (entry_isomorphism g i)).
Proof.
change (linking_compose L (bottom_inclusion c (index
  (DPNormalizerChainIndices.compose (selected_indices f) (selected_indices g)) i))
  (linking_compose L (iso_hom (@entry_equality_iso S F L c _ _
    (compose_index (selected_indices f) (selected_indices g) i)))
    (linking_compose L (iso_hom (entry_isomorphism f (index (selected_indices g) i)))
      (iso_hom (entry_isomorphism g i)))) =
  linking_compose L (bottom_arrow f (index (selected_indices g) i))
    (iso_hom (entry_isomorphism g i))).
rewrite -linking_assoc bottom_inclusion_chart -linking_assoc; reflexivity.
Qed.

Definition evaluation_arrow (c d : chain F) (f : chain_map L c d) := bottom_arrow f ord0.

Lemma evaluation_identity (c : chain F) :
  evaluation_arrow (identity_chain_map L c) = linking_identity L (entry c ord0).
Proof.
change (linking_compose L (bottom_inclusion c (index (DPNormalizerChainIndices.identity c) ord0))
  (iso_hom (@entry_equality_iso S F L c _ _ (@identity_index S F c ord0))) =
  linking_identity L (entry c ord0)).
by rewrite bottom_inclusion_chart bottom_inclusion_refl.
Qed.

Lemma evaluation_compose (c d t : chain F) (f : chain_map L c d) (g : chain_map L d t) :
  evaluation_arrow (composite_chain_map f g) =
  linking_compose L (evaluation_arrow f) (evaluation_arrow g).
Proof.
rewrite /evaluation_arrow bottom_arrow_composite.
rewrite -(@bottom_arrow_square c d f ord0 (index (selected_indices g) ord0) (leq0n _)).
rewrite linking_assoc; reflexivity.
Qed.

Definition evaluation : functor (chain_category L) (linking_category L).
Proof.
refine (@Build_functor (chain_category L) (linking_category L)
  (fun c => entry c ord0) (fun c d f => evaluation_arrow f) _ _).
- move=> c; exact: evaluation_identity.
- move=> c d t f g; exact: evaluation_compose.
Defined.

Lemma evaluation_object (c : chain F) : fobj evaluation c = entry c ord0.
Proof. reflexivity. Qed.

Lemma evaluation_map (c d : chain F) (f : chain_map L c d) :
  fmap evaluation f = linking_compose L (bottom_inclusion c (index (selected_indices f) ord0))
    (iso_hom (entry_isomorphism f ord0)).
Proof. reflexivity. Qed.

End Evaluation.
End DPNormalizerLinkingChainEvaluation.
