(** Actual target-automorphism comparison of two linking-chain maps.
    The selector-equality chart is retained explicitly in every component. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  CategoryAutomorphismConjugation LinkingChainRestrictionMaps LinkingChainTransportEqualities
  LinkingChainRestrictionIndependence LinkingChainRestrictionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps DPLinkingChainTransportEqualities
  DPLinkingChainRestrictionIndependence DPLinkingChainRestrictionUniqueness
  DPCategoryAutomorphismConjugation.
Local Open Scope group_scope.

Module DPLinkingChainTargetComparison.
Section Common.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable e : selector c d.
Variables a b : forall i : 'I_(length d).+1,
  @isomorphism (linking_category L) (entry c (index e i)) (entry d i).
Hypothesis ha : forall (i j : 'I_(length d).+1) (hij : i <= j),
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij)) (iso_hom (a j)) =
  linking_compose L (iso_hom (a i)) (@chain_inclusion S F L d i j hij).
Hypothesis hb : forall (i j : 'I_(length d).+1) (hij : i <= j),
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij)) (iso_hom (b j)) =
  linking_compose L (iso_hom (b i)) (@chain_inclusion S F L d i j hij).

Theorem common_comparison_component (i : 'I_(length d).+1) :
    linking_compose L (iso_hom (a i))
      (@projection S F L d i (@comparison_element S F L c d e a b ha hb)) = iso_hom (b i).
Proof.
rewrite comparison_element_component /comparison_component -linking_assoc.
have hi := iso_hom_inv (a i).
change (linking_compose L (iso_hom (a i)) (iso_inv (a i)) = linking_identity L (entry c (index e i))) in hi.
rewrite hi linking_id_left; reflexivity.
Qed.
End Common.

Section General.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variables f g : chain_map L c d.

Definition comparison_property (he : selected_indices f = selected_indices g)
    (a : chain_automorphism_group L d) : Prop :=
  forall i, linking_compose L (iso_hom (entry_isomorphism f i)) (@projection S F L d i a) =
    linking_compose L (iso_hom (@entry_equality_iso S F L c _ _
      (f_equal (fun e => index e i) he))) (iso_hom (entry_isomorphism g i)).

Definition comparison_with_selection (he : selected_indices f = selected_indices g) :
    {a : chain_automorphism_group L d | comparison_property he a}.
Proof.
unfold comparison_property.
case: f g he=> e a ha; case=> e' b hb /= he.
case: e' / he in b hb *.
exists (@comparison_element S F L c d e a b ha hb).
move=> i.
change (linking_compose L (iso_hom (a i))
  (@projection S F L d i (@comparison_element S F L c d e a b ha hb)) =
  linking_compose L (linking_identity L (entry c (index e i))) (iso_hom (b i))).
rewrite linking_id_left; exact: common_comparison_component.
Defined.

Definition target_comparison : chain_automorphism_group L d :=
  proj1_sig (comparison_with_selection (selected_indices_unique f g)).

Theorem target_comparison_property :
    comparison_property (selected_indices_unique f g) target_comparison.
Proof. exact: proj2_sig (comparison_with_selection (selected_indices_unique f g)). Qed.

Theorem comparison_property_unique (he : selected_indices f = selected_indices g)
    (a b : chain_automorphism_group L d)
    (ha : comparison_property he a) (hb : comparison_property he b) : a = b.
Proof.
apply projection_ext=> i.
apply (@iso_cancel_left (linking_category L) _ _ _ (entry_isomorphism f i)).
exact (Logic.eq_trans (ha i) (Logic.eq_sym (hb i))).
Qed.
End General.
End DPLinkingChainTargetComparison.
