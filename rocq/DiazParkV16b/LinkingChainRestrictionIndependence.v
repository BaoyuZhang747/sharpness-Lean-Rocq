(** Choice independence of genuine chain-automorphism cohomology maps.
    A compatible comparison tuple gives an actual group-functor natural
    transformation; the already-proved bar prism supplies equality. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  CategoryAutomorphismConjugation CategoryAutomorphismComparison LinkingChainRestrictionMaps
  GroupCohomologyBase GroupCohomologyFunctor GroupCohomologyPullback CategoryConstantCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps DPCategoryAutomorphismConjugation
  DPCategoryAutomorphismComparison DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback.
Local Open Scope group_scope.

Module DPLinkingChainRestrictionIndependence.
Section CommonSelection.
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
Local Notation f := (@Build_chain_map S F L c d e a ha).
Local Notation g := (@Build_chain_map S F L c d e b hb).
Local Notation G := (chain_automorphism_group L c).
Local Notation H := (chain_automorphism_group L d).

Definition comparison_component (i : 'I_(length d).+1) : automorphism_group L (entry d i) :=
  linking_compose L (iso_inv (a i)) (iso_hom (b i)).

Definition comparison_tuple : tuple_group L d := [ffun i => comparison_component i].

Lemma comparison_tuple_compatible : @compatible S F L d comparison_tuple.
Proof.
apply/compatibleP=> i j hij; rewrite /comparison_tuple !ffunE.
exact (@difference_square (linking_category L) _ _ _ _ (a i) (b i) (a j) (b j)
  (@chain_inclusion S F L c _ _ (index_mono e hij)) (@chain_inclusion S F L d i j hij)
  (@ha i j hij) (@hb i j hij)).
Qed.

Definition comparison_element : H.
Proof. apply: (Sub comparison_tuple); rewrite inE; exact comparison_tuple_compatible. Defined.

Lemma comparison_element_component i :
  @projection S F L d i comparison_element = comparison_component i.
Proof. change (comparison_tuple i = comparison_component i); by rewrite /comparison_tuple ffunE. Qed.

Lemma restriction_comparison (x : G) :
  restriction_morphism f x * comparison_element = comparison_element * restriction_morphism g x.
Proof.
apply projection_ext=> i.
have hp (u v : H) : @projection S F L d i (u * v) =
  @projection S F L d i u * @projection S F L d i v := tuple_mulE _ _ _.
rewrite !hp !restriction_morphism_component comparison_element_component !automorphism_mul.
exact (@conjugate_difference_intertwines (linking_category L) _ _ (a i) (b i)
  (@projection S F L c (index e i) x)).
Qed.

Definition restriction_comparison_nat_trans :
  nat_trans (group_functor (restriction_morphism f)) (group_functor (restriction_morphism g)).
Proof.
refine (@Build_nat_trans (group_category G) (group_category H)
  (group_functor (restriction_morphism f)) (group_functor (restriction_morphism g))
  (fun _ => comparison_element) _).
move=> x y u; exact: restriction_comparison.
Defined.

Theorem common_selection_pull_equal (R : comPzRingType) (A : lmodType R) n :
  pull A (restriction_morphism f) n = pull A (restriction_morphism g) n.
Proof.
symmetry; exact (@DPCategoryConstantCohomology.pull_nat_trans R A _ _ _ _
  restriction_comparison_nat_trans n).
Qed.
End CommonSelection.

Theorem restriction_pull_equal (S : finGroupType) (F : DPFusionSystem.system S)
    (L : DPCentricLinking.system F) (c d : chain F)
    (f g : chain_map L c d) (h : selected_indices f = selected_indices g)
    (R : comPzRingType) (A : lmodType R) n :
  pull A (restriction_morphism f) n = pull A (restriction_morphism g) n.
Proof.
case: f h=> e a ha; case: g=> e' b hb /= h.
case: e' / h in b hb *.
exact: common_selection_pull_equal.
Qed.
End DPLinkingChainRestrictionIndependence.
