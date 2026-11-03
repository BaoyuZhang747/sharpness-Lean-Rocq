(** Prefix deletion is monic in the actual linking-chain category. The omitted
    first component is recovered from the next compatibility square by the
    already proved monicity of linking inclusions. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import CategoryAutomorphismConjugation LinkingSystem
  LinkingSystemCancellation LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerPointedChainPrefix LinkingChainRestrictionMaps
  LinkingChainRestrictionOperations LinkingChainRestrictionUniqueness LinkingChainTransportEqualities
  NormalizerLinkingChainExt NormalizerLinkingEvaluationPrefix.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryAutomorphismConjugation DPCentricLinking DPLinkingCancellation
  DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndices
  DPNormalizerPointedChainPrefix DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations
  DPLinkingChainRestrictionUniqueness DPLinkingChainTransportEqualities
  DPNormalizerLinkingChainExt DPNormalizerLinkingEvaluationPrefix.

Module DPNormalizerLinkingEvaluationDeletionMonic.
Section Monic.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom d).
Let delta := deletion L hI.

Theorem deletion_monic (f g : chain_map L c (prepend hI)) :
  composite_chain_map f delta = composite_chain_map g delta -> f = g.
Proof.
have he := @selected_indices_unique S F L c (prepend hI) f g.
case: f he=> e a ha; case: g=> e' b hb /= he.
case: e' / he in b hb *.
move=> hcomp.
have retained (i : 'I_(length d).+1) :
    iso_hom (a (index (selected_indices delta) i)) =
    iso_hom (b (index (selected_indices delta) i)).
  apply (@compose_right_injective S F L _ _ _ (iso_hom (entry_isomorphism delta i))).
  apply (@iso_cancel_left (linking_category L) _ _ _
    (@entry_equality_iso S F L c _ _ (compose_index e (selected_indices delta) i))).
  exact (@chain_map_eq_same_entry S F L c d
    (DPNormalizerChainIndices.compose e (selected_indices delta)) _ _ _ _ hcomp i).
have retained_lift (i : 'I_(length d).+1) : iso_hom (a (lift ord0 i)) = iso_hom (b (lift ord0 i)).
  have hh := retained i.
  change (iso_hom (a (index (deletion_selector hI) i)) =
    iso_hom (b (index (deletion_selector hI) i))) in hh.
  by rewrite deletion_index in hh.
apply chain_map_ext_same=> i.
case: (unliftP ord0 i)=> [j ->|->]; first exact: retained_lift.
apply (@compose_right_injective S F L _ _ _
  (@chain_inclusion S F L (prepend hI) ord0 (lift ord0 ord0) (leq0n _))).
rewrite -(ha ord0 (lift ord0 ord0) (leq0n _))
  -(hb ord0 (lift ord0 ord0) (leq0n _)) retained_lift; reflexivity.
Qed.
End Monic.
End DPNormalizerLinkingEvaluationDeletionMonic.
