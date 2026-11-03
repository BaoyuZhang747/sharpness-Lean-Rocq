(** Genuine restriction and transport of compatible linking automorphisms.
    The selected components are conjugated by actual linking isomorphisms. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  CategoryAutomorphismConjugation.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains
  DPLinkingChainAutomorphisms DPNormalizerChainIndices DPCategoryAutomorphismConjugation.
Local Open Scope group_scope.

Module DPLinkingChainRestrictionMaps.
Section Maps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Record chain_map (c d : chain F) := {
  selected_indices : selector c d;
  entry_isomorphism : forall i : 'I_(length d).+1,
    @isomorphism (linking_category L) (entry c (index selected_indices i)) (entry d i);
  entry_square : forall (i j : 'I_(length d).+1) (hij : i <= j),
    linking_compose L (@chain_inclusion S F L c _ _ (index_mono selected_indices hij))
      (iso_hom (entry_isomorphism j)) =
    linking_compose L (iso_hom (entry_isomorphism i)) (@chain_inclusion S F L d i j hij)
}.

Variables c d : chain F.
Variable f : chain_map c d.
Local Notation G := (chain_automorphism_group L c).
Local Notation H := (chain_automorphism_group L d).

Definition restricted_component (a : G) (i : 'I_(length d).+1) : automorphism_group L (entry d i) :=
  @conjugate (linking_category L) _ _ (entry_isomorphism f i)
    (@projection S F L c (index (selected_indices f) i) a).

Lemma restricted_component_square (a : G) (i j : 'I_(length d).+1) (hij : i <= j) :
  linking_compose L (restricted_component a i) (@chain_inclusion S F L d i j hij) =
    linking_compose L (@chain_inclusion S F L d i j hij) (restricted_component a j).
Proof.
exact (@conjugate_square (linking_category L) _ _ _ _
  (entry_isomorphism f i) (entry_isomorphism f j)
  (@chain_inclusion S F L c _ _ (index_mono (selected_indices f) hij))
  (@chain_inclusion S F L d i j hij)
  (@projection S F L c (index (selected_indices f) i) a)
  (@projection S F L c (index (selected_indices f) j) a)
  (entry_square f hij) (@projection_square S F L c a _ _ (index_mono (selected_indices f) hij))).
Qed.

Definition restricted_tuple (a : G) : tuple_group L d := [ffun i => restricted_component a i].

Lemma restricted_tuple_compatible (a : G) : @compatible S F L d (restricted_tuple a).
Proof.
apply/compatibleP=> i j hij.
rewrite /restricted_tuple !ffunE; exact: restricted_component_square.
Qed.

Definition restriction (a : G) : H.
Proof.
apply: (Sub (restricted_tuple a)); rewrite inE; exact: restricted_tuple_compatible.
Defined.

Lemma restriction_component (a : G) i :
  @projection S F L d i (restriction a) = restricted_component a i.
Proof. change (restricted_tuple a i = restricted_component a i); by rewrite /restricted_tuple ffunE. Qed.

Lemma restriction_morphic : morphic [set: G] restriction.
Proof.
apply/morphicP=> a b _ _; apply projection_ext=> i.
have hp : @projection S F L d i (restriction a * restriction b) =
    @projection S F L d i (restriction a) * @projection S F L d i (restriction b) := tuple_mulE _ _ _.
rewrite hp !restriction_component.
rewrite /restricted_component.
have hq : @projection S F L c (index (selected_indices f) i) (a * b) =
  @projection S F L c (index (selected_indices f) i) a *
  @projection S F L c (index (selected_indices f) i) b := tuple_mulE _ _ _.
rewrite hq !automorphism_mul.
exact (@conjugate_compose (linking_category L) _ _ (entry_isomorphism f i)
  (@projection S F L c (index (selected_indices f) i) a)
  (@projection S F L c (index (selected_indices f) i) b)).
Qed.

Definition restriction_morphism : {morphism [set: G] >-> H} :=
  [morphism of morphm restriction_morphic].

Theorem restriction_morphism_component (a : G) i :
  @projection S F L d i (restriction_morphism a) =
  linking_compose L (iso_inv (entry_isomorphism f i))
    (linking_compose L (@projection S F L c (index (selected_indices f) i) a)
      (iso_hom (entry_isomorphism f i))).
Proof. exact: restriction_component. Qed.
End Maps.
End DPLinkingChainRestrictionMaps.
