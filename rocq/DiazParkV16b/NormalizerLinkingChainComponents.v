(** Actual linking-chain components in a specified equal source entry. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import CategoryAutomorphismConjugation LinkingSystem LinkingChainObjects NormalizerChainIndices
  LinkingChainRestrictionMaps LinkingChainTransportEqualities LinkingChainRestrictionOperations
  LinkingChainRestrictionUniqueness NormalizerLinkingChainExt.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryAutomorphismConjugation DPCentricLinking DPLinkingChains DPNormalizerChainIndices
  DPLinkingChainRestrictionMaps DPLinkingChainTransportEqualities
  DPLinkingChainRestrictionOperations DPLinkingChainRestrictionUniqueness
  DPNormalizerLinkingChainExt.

Module DPNormalizerLinkingChainComponents.
Section Components.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma entry_chart_loop (c : chain F) (i : 'I_(length c).+1) (h : i = i) :
  iso_hom (@entry_equality_iso S F L c i i h) = linking_identity L (entry c i).
Proof. have -> : h = Logic.eq_refl i := Prop_irrelevance _ _; reflexivity. Qed.

Lemma entry_chart_inverse (c : chain F) (i j : 'I_(length c).+1) (h : i = j) :
  linking_compose L (iso_hom (@entry_equality_iso S F L c j i (Logic.eq_sym h)))
    (iso_hom (@entry_equality_iso S F L c i j h)) = linking_identity L (entry c j).
Proof. case: j / h; exact: linking_id_left. Qed.

Lemma entry_chart_comp (c : chain F) (i j k : 'I_(length c).+1) (h : i = j) (h' : j = k) :
  linking_compose L (iso_hom (@entry_equality_iso S F L c i j h))
    (iso_hom (@entry_equality_iso S F L c j k h')) =
  iso_hom (@entry_equality_iso S F L c i k (eq_trans h h')).
Proof. case: j / h in h' *; case: k / h'; exact: linking_id_left. Qed.

Definition entry_at (c d : chain F) (f : chain_map L c d)
    (i : 'I_(length d).+1) (j : 'I_(length c).+1)
    (h : index (selected_indices f) i = j) : linking_hom L (entry c j) (entry d i) :=
  linking_compose L (iso_hom (@entry_equality_iso S F L c _ _ (Logic.eq_sym h)))
    (iso_hom (entry_isomorphism f i)).
Arguments entry_at {c d} f i j h.

Lemma entry_at_refl (c d : chain F) (f : chain_map L c d)
    (i : 'I_(length d).+1) (h : index (selected_indices f) i = index (selected_indices f) i) :
  entry_at f i _ h = iso_hom (entry_isomorphism f i).
Proof. by rewrite /entry_at entry_chart_loop linking_id_left. Qed.

Theorem chain_map_ext_at (c d : chain F) (f g : chain_map L c d)
    (j : 'I_(length d).+1 -> 'I_(length c).+1)
    (hf : forall i, index (selected_indices f) i = j i)
    (hg : forall i, index (selected_indices g) i = j i) :
  (forall i, entry_at f i (j i) (hf i) = entry_at g i (j i) (hg i)) -> f = g.
Proof.
have he : selected_indices f = selected_indices g.
  apply val_inj; apply/ffunP=> i; exact (eq_trans (hf i) (esym (hg i))).
move=> h; apply (@chain_map_ext S F L c d f g he)=> i.
apply (@iso_cancel_left (linking_category L)
  (entry c (j i)) (entry c (index (selected_indices f) i)) (entry d i)
  (@entry_equality_iso S F L c _ _ (esym (hf i)))).
change (linking_compose L (iso_hom (@entry_equality_iso S F L c _ _ (esym (hf i))))
  (linking_compose L (iso_hom (@entry_equality_iso S F L c _ _ (f_equal (fun e => index e i) he)))
    (iso_hom (entry_isomorphism g i))) =
  linking_compose L (iso_hom (@entry_equality_iso S F L c _ _ (esym (hf i))))
    (iso_hom (entry_isomorphism f i))).
rewrite -linking_assoc entry_chart_comp.
have hp : eq_trans (esym (hf i)) (f_equal (fun e => index e i) he) = esym (hg i) :=
  Prop_irrelevance _ _.
rewrite hp; exact: esym (h i).
Qed.

Lemma identity_entry_at (c : chain F) (i : 'I_(length c).+1)
    (h : index (selected_indices (identity_chain_map L c)) i = i) :
  entry_at (identity_chain_map L c) i i h = linking_identity L (entry c i).
Proof.
have he : h = @identity_index S F c i := Prop_irrelevance _ _.
rewrite he /entry_at; exact: entry_chart_inverse.
Qed.

Lemma composite_entry_at_native (c d t : chain F) (f : chain_map L c d) (g : chain_map L d t)
    (i : 'I_(length t).+1) :
  entry_at (composite_chain_map f g) i (index (selected_indices f) (index (selected_indices g) i))
    (compose_index (selected_indices f) (selected_indices g) i) =
  linking_compose L (iso_hom (entry_isomorphism f (index (selected_indices g) i)))
    (iso_hom (entry_isomorphism g i)).
Proof.
rewrite /entry_at /composite_chain_map /composite_entry_iso /=.
change (linking_compose L
  (iso_hom (@entry_equality_iso S F L c _ _ (esym (compose_index (selected_indices f) (selected_indices g) i))))
  (linking_compose L (iso_hom (@entry_equality_iso S F L c _ _ (compose_index (selected_indices f) (selected_indices g) i)))
    (linking_compose L (iso_hom (entry_isomorphism f (index (selected_indices g) i)))
      (iso_hom (entry_isomorphism g i)))) =
  linking_compose L (iso_hom (entry_isomorphism f (index (selected_indices g) i)))
    (iso_hom (entry_isomorphism g i))).
by rewrite -linking_assoc entry_chart_inverse linking_id_left.
Qed.

Theorem composite_entry_at (c d t : chain F) (f : chain_map L c d) (g : chain_map L d t)
    (i : 'I_(length t).+1) (k : 'I_(length d).+1) (j : 'I_(length c).+1)
    (hg : index (selected_indices g) i = k) (hf : index (selected_indices f) k = j)
    (h : index (selected_indices (composite_chain_map f g)) i = j) :
  entry_at (composite_chain_map f g) i j h =
  linking_compose L (entry_at f k j hf) (entry_at g i k hg).
Proof.
case: k / hg in hf h *; case: j / hf in h *.
have -> : h = compose_index (selected_indices f) (selected_indices g) i := Prop_irrelevance _ _.
rewrite !entry_at_refl; exact: composite_entry_at_native.
Qed.

End Components.
End DPNormalizerLinkingChainComponents.
