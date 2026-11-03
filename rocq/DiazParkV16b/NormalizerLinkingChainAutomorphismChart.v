(** The actual one-object automorphism chart of the linking-chain category.
    Its map is the compatible automorphism tuple, and restriction along
    every genuine chain morphism supplies an explicit natural transformation. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  LinkingChainRestrictionMaps LinkingChainRestrictionOperations LinkingChainTargetAction
  LinkingChainAutomorphismMaps LinkingChainTargetTorsor LinkingChainTargetComposition
  NormalizerLinkingChainCategory GroupCohomologyBase GroupCohomologyFunctor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations DPLinkingChainTargetAction
  DPLinkingChainAutomorphismMaps DPLinkingChainTargetTorsor DPLinkingChainTargetComposition
  DPNormalizerLinkingChainCategory DPGroupCohomology DPGroupCohomologyFunctor.
Local Open Scope group_scope.

Module DPNormalizerLinkingChainAutomorphismChart.
Section Chart.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma chain_compose_automorphism (c d : chain F) (f : chain_map L c d)
    (a : chain_automorphism_group L d) :
    composite_chain_map f (automorphism_chain_map a) = target_action f a.
Proof.
rewrite /automorphism_chain_map composite_target_action chain_compose_id_right; reflexivity.
Qed.

Lemma automorphism_chain_map_one (c : chain F) :
    @automorphism_chain_map S F L c 1 = identity_chain_map L c.
Proof. exact: target_action_one. Qed.

Lemma automorphism_chain_map_multiply (c : chain F)
    (a b : chain_automorphism_group L c) :
    automorphism_chain_map (a * b) =
    composite_chain_map (automorphism_chain_map a) (automorphism_chain_map b).
Proof.
rewrite chain_compose_automorphism /automorphism_chain_map target_action_multiply; reflexivity.
Qed.

Definition automorphism_chart (c : chain F) :
    functor (group_category (chain_automorphism_group L c)) (chain_category L).
Proof.
refine (@Build_functor (group_category (chain_automorphism_group L c)) (chain_category L)
  (fun _ => c) (fun _ _ a => automorphism_chain_map a) _ _).
- move=> x; exact: automorphism_chain_map_one.
- move=> x y z a b; exact: automorphism_chain_map_multiply.
Defined.

Lemma automorphism_chart_map (c : chain F) (a : chain_automorphism_group L c) :
    @fmap _ _ (automorphism_chart c) tt tt a = automorphism_chain_map a.
Proof. reflexivity. Qed.

Theorem automorphism_chart_faithful (c : chain F) (x y : group_category (chain_automorphism_group L c)) :
    injective (@fmap _ _ (automorphism_chart c) x y).
Proof. exact: automorphism_chain_map_injective. Qed.

Theorem automorphism_chart_full (c : chain F) (x y : group_category (chain_automorphism_group L c))
    (f : hom (chain_category L) (fobj (automorphism_chart c) x) (fobj (automorphism_chart c) y)) :
    exists a, @fmap _ _ (automorphism_chart c) x y a = f.
Proof. exact: automorphism_chain_map_surjective. Qed.

Definition restriction_chart_transformation (c d : chain F) (f : chain_map L c d) :
    nat_trans (automorphism_chart c)
      (functor_comp (group_functor (restriction_morphism f)) (automorphism_chart d)).
Proof.
refine (@Build_nat_trans (group_category (chain_automorphism_group L c)) (chain_category L)
  (automorphism_chart c)
  (functor_comp (group_functor (restriction_morphism f)) (automorphism_chart d))
  (fun _ => f) _).
move=> x y a.
change (composite_chain_map (automorphism_chain_map a) f =
  composite_chain_map f (automorphism_chain_map (restriction_morphism f a))).
rewrite chain_compose_automorphism /automorphism_chain_map
  composite_source_action chain_compose_id_left; reflexivity.
Defined.

Lemma restriction_chart_transformation_component (c d : chain F) (f : chain_map L c d) :
    component (restriction_chart_transformation f) tt = f.
Proof. reflexivity. Qed.
End Chart.
End DPNormalizerLinkingChainAutomorphismChart.
