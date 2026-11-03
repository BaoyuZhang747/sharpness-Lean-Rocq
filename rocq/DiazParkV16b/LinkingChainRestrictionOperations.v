(** Identities and composites of genuine linking-chain maps, with literal
    functoriality of their induced automorphism-group homomorphisms. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryAdjointUniqueness FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  CategoryAutomorphismConjugation LinkingChainRestrictionMaps LinkingChainTransportEqualities
  GroupCohomologyFunctor GroupCohomologyOrbitCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps DPLinkingChainTransportEqualities
  DPCategoryAutomorphismConjugation DPGroupCohomologyFunctor.
Local Open Scope group_scope.

Module DPLinkingChainRestrictionOperations.
Section Operations.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Definition identity_chain_map (c : chain F) : chain_map L c c.
Proof.
refine (@Build_chain_map S F L c c (DPNormalizerChainIndices.identity c)
  (fun i => @entry_equality_iso S F L c _ _ (@identity_index S F c i)) _).
move=> i j hij; exact: inclusion_equality_square.
Defined.

Lemma identity_restriction (c : chain F) :
  restriction_morphism (identity_chain_map c) = group_hom_identity (chain_automorphism_group L c).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext=> a.
apply projection_ext=> i.
rewrite restriction_morphism_component.
exact: projection_conjugate_equality.
Qed.

Variables c d t : chain F.
Variable f : chain_map L c d.
Variable g : chain_map L d t.
Local Notation e := (DPNormalizerChainIndices.compose (selected_indices f) (selected_indices g)).

Definition composite_entry_iso (i : 'I_(length t).+1) :
  @isomorphism (linking_category L) (entry c (index e i)) (entry t i) :=
  isomorphism_composition
    (@entry_equality_iso S F L c _ _ (compose_index (selected_indices f) (selected_indices g) i))
    (isomorphism_composition (entry_isomorphism f (index (selected_indices g) i))
      (entry_isomorphism g i)).

Lemma composite_entry_square (i j : 'I_(length t).+1) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij))
    (iso_hom (composite_entry_iso j)) =
  linking_compose L (iso_hom (composite_entry_iso i)) (@chain_inclusion S F L t i j hij).
Proof.
pose eqi := @entry_equality_iso S F L c _ _ (compose_index (selected_indices f) (selected_indices g) i).
pose eqj := @entry_equality_iso S F L c _ _ (compose_index (selected_indices f) (selected_indices g) j).
pose fi := entry_isomorphism f (index (selected_indices g) i).
pose fj := entry_isomorphism f (index (selected_indices g) j).
pose gi := entry_isomorphism g i.
pose gj := entry_isomorphism g j.
have h0 := @inclusion_equality_square S F L c _ _ _ _
  (compose_index (selected_indices f) (selected_indices g) i)
  (compose_index (selected_indices f) (selected_indices g) j)
  (index_mono e hij) (index_mono (selected_indices f) (index_mono (selected_indices g) hij)).
have h1 := entry_square f (index_mono (selected_indices g) hij).
have h2 := entry_square g hij.
change (linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij))
  (linking_compose L (iso_hom eqj) (linking_compose L (iso_hom fj) (iso_hom gj))) =
  linking_compose L (linking_compose L (iso_hom eqi)
    (linking_compose L (iso_hom fi) (iso_hom gi))) (@chain_inclusion S F L t i j hij)).
rewrite -(@linking_assoc S F L _ _ _ _
  (@chain_inclusion S F L c _ _ (index_mono e hij))
  (iso_hom eqj) (linking_compose L (iso_hom fj) (iso_hom gj))) h0 !linking_assoc.
rewrite -(@linking_assoc S F L _ _ _ _
  (@chain_inclusion S F L c _ _ (index_mono (selected_indices f) (index_mono (selected_indices g) hij)))
  (iso_hom fj) (iso_hom gj)) h1 !linking_assoc h2.
reflexivity.
Qed.

Definition composite_chain_map : chain_map L c t :=
  @Build_chain_map S F L c t e composite_entry_iso composite_entry_square.

Theorem composite_restriction :
  restriction_morphism composite_chain_map =
    group_hom_comp (restriction_morphism f) (restriction_morphism g).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext=> a.
apply projection_ext=> i.
change (@projection S F L t i (restriction_morphism composite_chain_map a) =
  @projection S F L t i (restriction_morphism g (restriction_morphism f a))).
rewrite (@restriction_morphism_component S F L c t composite_chain_map a i).
change (conjugate (composite_entry_iso i) (@projection S F L c (index e i) a) =
  @projection S F L t i (restriction_morphism g (restriction_morphism f a))).
rewrite /composite_entry_iso !conjugate_iso_composition projection_conjugate_equality.
rewrite restriction_morphism_component.
change (conjugate (entry_isomorphism g i)
  (conjugate (entry_isomorphism f (index (selected_indices g) i))
    (@projection S F L c (index (selected_indices f) (index (selected_indices g) i)) a)) =
  conjugate (entry_isomorphism g i)
    (@projection S F L d (index (selected_indices g) i) (restriction_morphism f a))).
rewrite restriction_morphism_component; reflexivity.
Qed.
End Operations.
End DPLinkingChainRestrictionOperations.
