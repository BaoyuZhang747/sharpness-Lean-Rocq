(** The actual normalizer ordinary-cohomology diagram. Every arrow is the
    native pullback of restriction and compatible linking conjugation;
    choice independence proves descent and functoriality on the quotient. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryModules FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainRelations NormalizerChainIndexCategory LinkingChainRestrictionMaps
  LinkingChainRestrictionUniqueness LinkingChainRestrictionOperations LinkingChainWitnessLift
  GroupCohomologyBase GroupCohomologyPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainRelations DPNormalizerChainIndex DPLinkingChainRestrictionMaps
  DPLinkingChainRestrictionUniqueness DPLinkingChainRestrictionOperations DPLinkingChainWitnessLift
  DPGroupCohomology DPGroupCohomologyPullback.

Module DPNormalizerOrdinaryCoefficient.
Section Representatives.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable representative : index_object F -> chain F.
Hypothesis representative_class : forall d, chain_class (representative d) = d.
Local Notation I := (index_category F).

Lemma arrow_witness_exists (d e : I) (u : hom I d e) :
  exists a : chain_witness (representative d) (representative e), True.
Proof.
have h := hom_relation u.
rewrite -(representative_class d) -(representative_class e) class_relation in h.
have /subconjugateP [a] := h; exists a; exact Logic.I.
Qed.

Definition arrow_witness (d e : I) (u : hom I d e) :
  chain_witness (representative d) (representative e) :=
  proj1_sig (cid (arrow_witness_exists u)).

Definition arrow_chain_map (d e : I) (u : hom I d e) :
  chain_map L (representative d) (representative e) :=
  witness_chain_map L (arrow_witness u).

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Definition representative_coefficient : module_codiagram R I.
Proof.
refine (@Build_functor (opposite I) (module_category R)
  (fun d => value R (chain_automorphism_group L (representative d)) A n)
  (fun d e u => pull A (restriction_morphism (arrow_chain_map u)) n) _ _).
- move=> d.
  rewrite (@chain_map_pull_unique S F L _ _ (arrow_chain_map (identity d))
    (identity_chain_map L (representative d)) R A n).
  rewrite identity_restriction pull_identity; reflexivity.
- move=> d e t u v.
  change (pull A (restriction_morphism (arrow_chain_map (@Category.compose I t e d v u))) n =
    module_hom_comp (pull A (restriction_morphism (arrow_chain_map u)) n)
      (pull A (restriction_morphism (arrow_chain_map v)) n)).
  rewrite (@chain_map_pull_unique S F L _ _
    (arrow_chain_map (@Category.compose I t e d v u))
    (composite_chain_map (arrow_chain_map v) (arrow_chain_map u)) R A n).
  rewrite composite_restriction pull_composition; reflexivity.
Defined.

Theorem representative_coefficient_map (d e : I) (u : hom I d e)
    (f : chain_map L (representative d) (representative e)) :
  @fmap _ _ representative_coefficient e d u = pull A (restriction_morphism f) n.
Proof. exact: chain_map_pull_unique. Qed.
End Representatives.

Definition canonical_representative (S : finGroupType) (F : DPFusionSystem.system S)
    (d : index_object F) : chain F := repr d.

Lemma canonical_representative_class (S : finGroupType) (F : DPFusionSystem.system S)
    (d : index_object F) : chain_class (canonical_representative d) = d.
Proof. exact: reprK. Qed.

Definition coefficient (S : finGroupType) (F : DPFusionSystem.system S)
    (L : DPCentricLinking.system F) (R : comPzRingType) (A : lmodType R) n :
  module_codiagram R (index_category F) :=
  @representative_coefficient S F L (@canonical_representative S F)
    (@canonical_representative_class S F) R A n.
End DPNormalizerOrdinaryCoefficient.
