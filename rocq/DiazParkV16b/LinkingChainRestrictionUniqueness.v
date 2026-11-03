(** Every genuine linking map between fixed strict chains chooses the same
    entries. Hence its native cohomology pullback is completely independent
    of the chosen compatible linking isomorphisms. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerProjectionCommaSelection LinkingChainRestrictionMaps
  LinkingChainRestrictionIndependence GroupCohomologyPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPNormalizerChainIndices
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionIndependence DPGroupCohomologyPullback.
Local Open Scope group_scope.

Module DPLinkingChainRestrictionUniqueness.
Section Uniqueness.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma linking_hom_card_le (P Q : DPFusionOrbit.centric_object F) (f : linking_hom L P Q) :
  #|val P| <= #|val Q|.
Proof.
have h := subset_leq_card (DPFusion.map_range (val (linking_projection L f))).
rewrite (card_in_imset (@DPFusion.map_injective S (val P) (val Q)
  (val (linking_projection L f)))) in h.
exact h.
Qed.

Lemma linking_iso_card (P Q : DPFusionOrbit.centric_object F)
    (e : @isomorphism (linking_category L) P Q) : #|val P| = #|val Q|.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: linking_hom_card_le (iso_hom e).
- exact: linking_hom_card_le (iso_inv e).
Qed.

Theorem selected_indices_unique (c d : chain F) (f g : chain_map L c d) :
  selected_indices f = selected_indices g.
Proof.
apply val_inj; apply/ffunP=> i.
apply: (@DPNormalizerProjectionCommaSelection.entry_card_injective S F c).
rewrite (@linking_iso_card _ _ (entry_isomorphism f i))
  (@linking_iso_card _ _ (entry_isomorphism g i)); reflexivity.
Qed.

Theorem chain_map_pull_unique (c d : chain F) (f g : chain_map L c d)
    (R : comPzRingType) (A : lmodType R) n :
  pull A (restriction_morphism f) n = pull A (restriction_morphism g) n.
Proof. exact (@restriction_pull_equal S F L c d f g (selected_indices_unique f g) R A n). Qed.
End Uniqueness.
End DPLinkingChainRestrictionUniqueness.
