(** Literal comparison with fusion conjugacy of an actual selected subchain. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainExtensions NormalizerChainRelations NormalizerChainConjugacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChainIndices DPNormalizerChainExtensions
  DPNormalizerChainRelations DPNormalizerChainConjugacy.
Local Open Scope group_scope.

Module DPNormalizerChainSubconjugacy.
Section Subconjugacy.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.

Definition selected_identity (e : selector c d) : selector (selected_chain e) d.
Proof.
apply: (Sub [ffun i => i]); apply/increasingP=> i j hij; by rewrite !ffunE.
Defined.

Lemma selected_identity_index (e : selector c d) i : index (selected_identity e) i = i.
Proof. exact: ffunE. Qed.

Definition selected_witness (a : chain_witness c d) :
  chain_witness (selected_chain (indices a)) d.
Proof.
refine (@Build_extension S F (selected_chain (indices a)) d 1%G 1%G
  (DPFusion.identity 1%G) (selected_identity (indices a)) (carrier a)
  (acting_sub a) _ (extension_map a) (extension_allowed a) (on_acting a) _).
- rewrite selected_identity_index /subgroup selected_chain_entry; exact: chain_sub a.
- move=> i; rewrite selected_identity_index /subgroup selected_chain_entry; exact: entry_images a i.
Defined.

Lemma selected_witness_conjugate (a : chain_witness c d) :
  conjugate (selected_chain (indices a)) d.
Proof.
apply/conjugateP; exists (selected_witness a).
exists (fun i => i); move=> i; exact: selected_identity_index.
Qed.

Definition subchain_witness (e : selector c d) : chain_witness c (selected_chain e).
Proof.
refine (@Build_extension S F c (selected_chain e) 1%G 1%G (DPFusion.identity 1%G)
  e (val (top c)) (sub1G _) (@entry_sub_top S F c _)
  (inclusion (subsetT (val (top c)))) (DPFusionSystem.inclusion_allowed F _) _ _).
- move=> x /set1P ->; by rewrite !map_one.
- move=> i; rewrite /subgroup selected_chain_entry.
  apply/setP=> y; apply/morphimP/idP.
  + move=> [x hx hxi ->]; by rewrite map_morphismE inclusion_in.
  + move=> hy; have hx := subsetP (@entry_sub_top S F c (index e i)) _ hy.
    exists y=> //; by rewrite map_morphismE inclusion_in.
Defined.

Theorem subconjugate_selected_iff : subconjugate c d <->
  exists e : selector c d, conjugate (selected_chain e) d.
Proof.
split.
- move/subconjugateP=> [a]; exists (indices a); exact: selected_witness_conjugate.
- move=> [e he]; apply: subconjugate_trans (conjugate_subconjugate he).
  exact: extension_subconjugate (subchain_witness e).
Qed.

End Subconjugacy.
End DPNormalizerChainSubconjugacy.
