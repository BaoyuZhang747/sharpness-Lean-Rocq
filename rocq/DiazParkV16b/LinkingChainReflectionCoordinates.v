(** Actual automorphism coordinates for a family of maps into one chain.
    The functor and natural transformation are built from the free
    transitive target action, not supplied as reflection hypotheses. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  LinkingChainRestrictionMaps LinkingChainRestrictionOperations LinkingChainTargetAction
  LinkingChainTargetComparison LinkingChainTargetTorsor LinkingChainTargetComposition LinkingChainAutomorphismMaps
  LinkingChainTargetComparisonLaws NormalizerLinkingChainCategory
  NormalizerLinkingChainAutomorphismChart GroupCohomologyBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations DPLinkingChainTargetAction
  DPLinkingChainTargetComparison DPLinkingChainTargetTorsor DPLinkingChainTargetComposition
  DPLinkingChainTargetComparisonLaws DPNormalizerLinkingChainCategory
  DPNormalizerLinkingChainAutomorphismChart DPGroupCohomology.
Local Open Scope group_scope.

Module DPLinkingChainReflectionCoordinates.
Section Coordinates.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable C : category.
Variable U : functor C (chain_category L).
Variable r : chain F.
Variable base : forall X : C, chain_map L (fobj U X) r.

Definition reflection_map (X Y : C) (f : hom C X Y) : chain_automorphism_group L r :=
  target_comparison (base X) (composite_chain_map (fmap U f) (base Y)).

Lemma reflection_identity (X : C) : reflection_map (identity X) = 1.
Proof.
rewrite /reflection_map fmap_id.
change (target_comparison (base X)
  (composite_chain_map (identity_chain_map L (fobj U X)) (base X)) = 1).
rewrite chain_compose_id_left; exact: target_comparison_identity.
Qed.

Lemma reflection_compose (X Y Z : C) (f : hom C X Y) (g : hom C Y Z) :
    reflection_map (compose f g) = reflection_map f * reflection_map g.
Proof.
rewrite /reflection_map fmap_compose.
change (target_comparison (base X)
  (composite_chain_map (composite_chain_map (fmap U f) (fmap U g)) (base Z)) =
  target_comparison (base X) (composite_chain_map (fmap U f) (base Y)) *
  target_comparison (base Y) (composite_chain_map (fmap U g) (base Z))).
rewrite chain_compose_assoc.
rewrite (target_comparison_cocycle (base X) (composite_chain_map (fmap U f) (base Y))
  (composite_chain_map (fmap U f) (composite_chain_map (fmap U g) (base Z)))).
rewrite target_comparison_precompose; reflexivity.
Qed.

Definition reflection : functor C (group_category (chain_automorphism_group L r)).
Proof.
refine (@Build_functor C (group_category (chain_automorphism_group L r))
  (fun _ => tt) (fun X Y f => reflection_map f) _ _).
- exact: reflection_identity.
- exact: reflection_compose.
Defined.

Lemma reflection_triangle (X Y : C) (f : hom C X Y) :
    composite_chain_map (base X) (DPLinkingChainAutomorphismMaps.automorphism_chain_map (reflection_map f)) =
    composite_chain_map (fmap U f) (base Y).
Proof. rewrite chain_compose_automorphism; exact: target_action_transitive. Qed.

Definition reflection_transformation :
    nat_trans U (functor_comp reflection (automorphism_chart L r)).
Proof.
refine (@Build_nat_trans C (chain_category L) U
  (functor_comp reflection (automorphism_chart L r)) base _).
move=> X Y f; symmetry; exact: reflection_triangle.
Defined.

Lemma reflection_transformation_component (X : C) :
    component reflection_transformation X = base X.
Proof. reflexivity. Qed.
End Coordinates.
End DPLinkingChainReflectionCoordinates.
