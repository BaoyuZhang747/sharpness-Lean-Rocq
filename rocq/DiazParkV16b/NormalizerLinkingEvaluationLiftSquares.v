(** The square for every retained entry of a linking-chain image-prefix lift.
    The first square is prescribed; all later squares follow from the actual
    compatible linking ladder and composition of distinguished inclusions. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices LinkingChainRestrictionMaps.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps.

Module DPNormalizerLinkingEvaluationLiftSquares.
Section Squares.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Lemma inclusion_compose_any (P Q R : Obj) (hPQ : val P \subset val Q)
    (hQR : val Q \subset val R) (hPR : val P \subset val R) :
  linking_compose L (inclusion L hPQ) (inclusion L hQR) = inclusion L hPR.
Proof.
change (@Category.compose (linking_category L) P Q R (inclusion L hPQ) (inclusion L hQR) = inclusion L hPR).
rewrite inclusion_compose; congr (inclusion L _); exact: Prop_irrelevance.
Qed.

Variables c d : chain F.
Variable f : chain_map L c d.
Variable I : Obj.
Hypothesis hI : val I \subset val (bottom d).
Variable b : @isomorphism (linking_category L) (bottom c) I.
Hypothesis first_square :
  linking_compose L (@chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) ord0)))
    (iso_hom (entry_isomorphism f ord0)) =
  linking_compose L (iso_hom b) (inclusion L hI).

Definition prefix_sub_entry (j : 'I_(length d).+1) : val I \subset val (entry d j) :=
  subset_trans hI (@entry_mono S F d ord0 j (leq0n j)).

Theorem prefix_entry_square (j : 'I_(length d).+1) :
  linking_compose L (@chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) j)))
    (iso_hom (entry_isomorphism f j)) =
  linking_compose L (iso_hom b) (inclusion L (prefix_sub_entry j)).
Proof.
have hi := @inclusion_compose_any (bottom c)
  (entry c (index (selected_indices f) ord0)) (entry c (index (selected_indices f) j))
  (@entry_mono S F c ord0 _ (leq0n (index (selected_indices f) ord0)))
  (@entry_mono S F c _ _ (@index_mono S F c d (selected_indices f) ord0 j (leq0n j)))
  (@entry_mono S F c ord0 _ (leq0n (index (selected_indices f) j))).
change (linking_compose L
  (@chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) ord0)))
  (@chain_inclusion S F L c _ _ (@index_mono S F c d (selected_indices f) ord0 j (leq0n j))) =
  @chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) j))) in hi.
rewrite -hi linking_assoc (@entry_square S F L c d f ord0 j (leq0n j)) -linking_assoc first_square linking_assoc.
congr (linking_compose L (iso_hom b) _).
exact: inclusion_compose_any.
Qed.
End Squares.
End DPNormalizerLinkingEvaluationLiftSquares.
