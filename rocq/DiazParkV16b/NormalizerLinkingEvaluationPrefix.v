(** Native linking-chain deletion from a strict image prefix. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerPointedChainPrefix LinkingChainRestrictionMaps
  LinkingChainRestrictionUniqueness.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPNormalizerPointedChainPrefix DPLinkingChainRestrictionMaps
  DPLinkingChainRestrictionUniqueness.

Module DPNormalizerLinkingEvaluationPrefix.
Section Equalities.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition object_equality_iso (P Q : Obj) (h : P = Q) :
    @isomorphism (linking_category L) P Q :=
  match h with Logic.eq_refl => @iso_refl (linking_category L) P end.

Lemma inclusion_equality_square (P Q P' Q' : Obj)
    (hP : P = P') (hQ : Q = Q') (hPQ : val P \subset val Q)
    (hPQ' : val P' \subset val Q') :
  linking_compose L (inclusion L hPQ) (iso_hom (object_equality_iso hQ)) =
  linking_compose L (iso_hom (object_equality_iso hP)) (inclusion L hPQ').
Proof.
case: P' / hP in hPQ' *; case: Q' / hQ in hPQ' *.
have -> : hPQ' = hPQ := Prop_irrelevance _ _.
change (linking_compose L (inclusion L hPQ) (linking_identity L Q) =
  linking_compose L (linking_identity L P) (inclusion L hPQ)).
by rewrite linking_id_left linking_id_right.
Qed.

Variable c : chain F.
Variable I : Obj.
Hypothesis hI : val I \proper val (bottom c).

Lemma deletion_entry_equality i : entry (prepend hI) (index (deletion_selector hI) i) = entry c i.
Proof. rewrite deletion_index; exact: prepend_entry_lift. Qed.

Definition deletion_entry_iso i : @isomorphism (linking_category L)
    (entry (prepend hI) (index (deletion_selector hI) i)) (entry c i) :=
  object_equality_iso (deletion_entry_equality i).

Lemma deletion_entry_square (i j : 'I_(length c).+1) (hij : i <= j) :
  linking_compose L
    (@chain_inclusion S F L (prepend hI) _ _ (index_mono (deletion_selector hI) hij))
    (iso_hom (deletion_entry_iso j)) =
  linking_compose L (iso_hom (deletion_entry_iso i)) (@chain_inclusion S F L c i j hij).
Proof. exact: inclusion_equality_square. Qed.

Definition deletion : chain_map L (prepend hI) c :=
  @Build_chain_map S F L (prepend hI) c (deletion_selector hI)
    deletion_entry_iso deletion_entry_square.

Lemma deletion_indices : selected_indices deletion = deletion_selector hI.
Proof. reflexivity. Qed.

Lemma deletion_entry i : entry_isomorphism deletion i = deletion_entry_iso i.
Proof. reflexivity. Qed.
End Equalities.

Section PositiveSelection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable f : chain_map L c d.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom d).
Variable b : @isomorphism (linking_category L) (bottom c) I.

Lemma selected_bottom_positive : 0 < index (selected_indices f) ord0.
Proof.
apply/negPn/negP=> hn.
have hz : index (selected_indices f) ord0 = ord0.
  apply val_inj; apply/eqP; rewrite -leqn0 leqNgt; exact hn.
have hc := @linking_iso_card S F L _ _ b.
have hd := @linking_iso_card S F L _ _ (entry_isomorphism f ord0).
rewrite hz in hd.
have hi := proper_card hI.
change (#|val (bottom c)| = #|val (bottom d)|) in hd.
by rewrite -hc hd ltnn in hi.
Qed.
End PositiveSelection.
End DPNormalizerLinkingEvaluationPrefix.
