(** Extensionality of genuine compatible linking-chain maps, including the
    actual equality charts between selected source entries. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainIndices
  LinkingChainRestrictionMaps LinkingChainTransportEqualities.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPNormalizerChainIndices
  DPLinkingChainRestrictionMaps DPLinkingChainTransportEqualities.

Module DPNormalizerLinkingChainExt.

Lemma isomorphism_hom_ext {C : category} {x y : C} (e f : @isomorphism C x y) :
  iso_hom e = iso_hom f -> e = f.
Proof.
case: e=> a b hab hba; case: f=> a' c hac hca /= h; subst a'.
have he : b = c.
  rewrite -(compose_id_right b) -hac -compose_assoc hba compose_id_left; reflexivity.
subst c; f_equal; apply Prop_irrelevance.
Qed.

Section Extensionality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.

Lemma chain_map_ext_same (e : selector c d)
    (a b : forall i : 'I_(length d).+1,
      @isomorphism (linking_category L) (entry c (index e i)) (entry d i))
    ha hb :
  (forall i, iso_hom (a i) = iso_hom (b i)) ->
  @Build_chain_map S F L c d e a ha = @Build_chain_map S F L c d e b hb.
Proof.
move=> h.
have he : a = b.
  apply functional_extensionality_dep=> i; apply isomorphism_hom_ext; exact: h.
subst b; f_equal; apply Prop_irrelevance.
Qed.

Theorem chain_map_ext (f g : chain_map L c d)
    (he : selected_indices f = selected_indices g) :
  (forall i, linking_compose L
    (iso_hom (@entry_equality_iso S F L c _ _ (f_equal (fun e => index e i) he)))
    (iso_hom (entry_isomorphism g i)) = iso_hom (entry_isomorphism f i)) -> f = g.
Proof.
case: f he=> e a ha; case: g=> e' b hb /= he.
case: e' / he in b hb *.
move=> h; apply chain_map_ext_same=> i.
have hi := h i.
change (linking_compose L (linking_identity L (entry c (index e i)))
  (iso_hom (b i)) = iso_hom (a i)) in hi.
rewrite linking_id_left in hi; exact: esym hi.
Qed.

Theorem chain_map_eq_entry (f g : chain_map L c d) (h : f = g) i :
  linking_compose L
    (iso_hom (@entry_equality_iso S F L c _ _
      (f_equal (fun e => index e i) (f_equal (@selected_indices S F L c d) h))))
    (iso_hom (entry_isomorphism g i)) = iso_hom (entry_isomorphism f i).
Proof.
case: g / h.
change (linking_compose L (linking_identity L (entry c (index (selected_indices f) i)))
  (iso_hom (entry_isomorphism f i)) = iso_hom (entry_isomorphism f i)).
exact: linking_id_left.
Qed.

Theorem chain_map_eq_same_entry (e : selector c d)
    (a b : forall i : 'I_(length d).+1,
      @isomorphism (linking_category L) (entry c (index e i)) (entry d i)) ha hb
    (h : @Build_chain_map S F L c d e a ha = @Build_chain_map S F L c d e b hb) i :
  iso_hom (a i) = iso_hom (b i).
Proof.
have hi := chain_map_eq_entry h i.
have hp : f_equal (@selected_indices S F L c d) h = Logic.eq_refl e :=
  Prop_irrelevance _ _.
rewrite hp in hi.
change (linking_compose L (linking_identity L (entry c (index e i)))
  (iso_hom (b i)) = iso_hom (a i)) in hi.
rewrite linking_id_left in hi; exact: esym hi.
Qed.

End Extensionality.
End DPNormalizerLinkingChainExt.
