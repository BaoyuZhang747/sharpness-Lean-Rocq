(** The actual costructured fibre of the linking-chain projection reflects
    onto the one-object group of compatible automorphisms of a representative.
    The coordinate functor comes from genuine linking-chain maps. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainRelations NormalizerChainIndexCategory LinkingChainRestrictionMaps
  LinkingChainRestrictionOperations LinkingChainWitnessLift LinkingChainTargetAction
  LinkingChainAutomorphismMaps LinkingChainTargetTorsor LinkingChainTargetComparison
  NormalizerLinkingChainCategory NormalizerLinkingChainProjection
  NormalizerLinkingChainAutomorphismChart LinkingChainReflectionCoordinates GroupCohomologyBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainRelations DPNormalizerChainIndex DPLinkingChainRestrictionMaps
  DPLinkingChainRestrictionOperations DPLinkingChainWitnessLift DPLinkingChainTargetAction
  DPLinkingChainAutomorphismMaps DPLinkingChainTargetTorsor DPLinkingChainTargetComparison
  DPNormalizerLinkingChainCategory DPNormalizerLinkingChainAutomorphismChart DPGroupCohomology.
Local Open Scope group_scope.

Module DPNormalizerLinkingCommaReflection.
Section Reflection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable d : index_category F.
Variable r : chain F.
Hypothesis hr : chain_class r = d.
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).
Local Notation C := (costructured_category P d).
Local Notation G := (group_category (chain_automorphism_group L r)).

Definition comparison_object : C.
Proof.
refine (@Build_costructured_object (chain_category L) (index_category F) P d r _).
apply hom_of_relation; change (index_relation (chain_class r) d).
rewrite -hr; exact: index_relation_refl.
Defined.

Definition comparison_arrow (a : chain_automorphism_group L r) :
    hom C comparison_object comparison_object.
Proof.
refine (@Build_costructured_hom (chain_category L) (index_category F) P d
  comparison_object comparison_object (automorphism_chain_map a) _).
exact: index_hom_unique.
Defined.

Definition comparison : functor G C.
Proof.
refine (@Build_functor G C (fun _ => comparison_object) (fun _ _ a => comparison_arrow a) _ _).
- move=> x; apply costructured_hom_ext; exact: automorphism_chain_map_one.
- move=> x y z a b; apply costructured_hom_ext; exact: automorphism_chain_map_multiply.
Defined.

Lemma base_witness_exists (X : C) :
    exists a : chain_witness (costructured_source X) r, True.
Proof.
have h := hom_relation (costructured_arrow X).
change (is_true (index_relation (chain_class (costructured_source X)) d)) in h.
rewrite -hr class_relation in h.
have /subconjugateP [a] := h; exists a; exact Logic.I.
Qed.

Definition base (X : C) : chain_map L (costructured_source X) r :=
  witness_chain_map L (proj1_sig (cid (base_witness_exists X))).

Definition base_arrow (X : C) : hom C X comparison_object.
Proof.
refine (@Build_costructured_hom (chain_category L) (index_category F) P d
  X comparison_object (base X) _).
exact: index_hom_unique.
Defined.

Definition reflection : functor C G :=
  @DPLinkingChainReflectionCoordinates.reflection S F L C (costructured_projection P d) r base.

Definition reflection_map (X Y : C) (f : hom C X Y) : chain_automorphism_group L r :=
  @fmap C G reflection X Y f.

Lemma reflection_triangle (X Y : C) (f : hom C X Y) :
    composite_chain_map (base X) (automorphism_chain_map (reflection_map f)) =
    composite_chain_map (costructured_map f) (base Y).
Proof.
exact (@DPLinkingChainReflectionCoordinates.reflection_triangle S F L C
  (costructured_projection P d) r base X Y f).
Qed.

Lemma reflection_action (X Y : C) (f : hom C X Y) :
    target_action (base X) (reflection_map f) =
    composite_chain_map (costructured_map f) (base Y).
Proof. rewrite -chain_compose_automorphism; exact: reflection_triangle. Qed.

Definition reflection_unit : nat_trans (functor_id C) (functor_comp reflection comparison).
Proof.
refine (@Build_nat_trans C C (functor_id C) (functor_comp reflection comparison) base_arrow _).
move=> X Y f; apply costructured_hom_ext; symmetry; exact: reflection_triangle.
Defined.

Lemma comparison_source : costructured_source comparison_object = r.
Proof. reflexivity. Qed.

Lemma comparison_arrow_map (a : chain_automorphism_group L r) :
    costructured_map (comparison_arrow a) = automorphism_chain_map a.
Proof. reflexivity. Qed.
End Reflection.
End DPNormalizerLinkingCommaReflection.
