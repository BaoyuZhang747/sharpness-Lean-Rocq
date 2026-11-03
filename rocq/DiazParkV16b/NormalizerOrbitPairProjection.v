(** The actual projection from normalized subgroup/chain pairs to the
    finite normalizer indexing category, with literal object and arrow maps. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainRelations NormalizerChainConjugacy NormalizerChainSubconjugacy
  NormalizerChainIndexCategory NormalizerOrbitPairCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndices DPNormalizerChainRelations
  DPNormalizerChainIndex DPNormalizerOrbitPair.

Module DPNormalizerOrbitPairProjection.
Section Projection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma pair_arrow_subconjugate (A B : DPNormalizerOrbitPair.object F)
    (f : pair_hom A B) : subconjugate (chain_of A) (chain_of B).
Proof.
have [g [_ [a]]] := hom_compatible f; exact: extension_subconjugate a.
Qed.

Definition projection_map (A B : DPNormalizerOrbitPair.object F) (f : pair_hom A B) :
  index_hom (chain_class (chain_of A)) (chain_class (chain_of B)).
Proof.
apply: hom_of_relation; rewrite class_relation; exact: pair_arrow_subconjugate f.
Defined.

Definition projection : functor (pair_category F) (index_category F).
Proof.
refine (@Build_functor (pair_category F) (index_category F)
  (fun A => chain_class (chain_of A)) (fun A B f => projection_map f) _ _).
- move=> A; exact: index_hom_unique.
- move=> A B C f g; exact: index_hom_unique.
Defined.

Lemma projection_object (A : DPNormalizerOrbitPair.object F) :
  fobj projection A = chain_class (chain_of A).
Proof. reflexivity. Qed.

Lemma projection_length (A B : DPNormalizerOrbitPair.object F) (f : pair_hom A B) :
  length (chain_of B) <= length (chain_of A).
Proof. exact: subconjugate_length (pair_arrow_subconjugate f). Qed.

Definition subchain_arrow (c d : chain F) (e : selector c d) :
  index_hom (chain_class c) (chain_class (selected_chain e)).
Proof.
apply: hom_of_relation; rewrite class_relation.
exact: extension_subconjugate (DPNormalizerChainSubconjugacy.subchain_witness e).
Defined.

Theorem class_arrow_iff_selected (c d : chain F) :
  inhabited (index_hom (chain_class c) (chain_class d)) <->
    exists e : selector c d, DPNormalizerChainConjugacy.conjugate (selected_chain e) d.
Proof.
split.
- move=> [f]; have h := hom_relation f; rewrite class_relation in h.
  exact: (proj1 (DPNormalizerChainSubconjugacy.subconjugate_selected_iff c d)) h.
- move=> h; apply: inhabits; apply: hom_of_relation; rewrite class_relation.
  exact: (proj2 (DPNormalizerChainSubconjugacy.subconjugate_selected_iff c d)) h.
Qed.

End Projection.
End DPNormalizerOrbitPairProjection.
