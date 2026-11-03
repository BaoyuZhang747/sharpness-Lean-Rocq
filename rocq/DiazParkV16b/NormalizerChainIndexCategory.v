(** The actual finite quotient indexing category: chain fusion-conjugacy
    classes, with arrows toward conjugates of selected subchains. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryFinite FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainRelations NormalizerChainConjugacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainRelations.
Local Open Scope quotient_scope.

Module DPNormalizerChainIndex.
Section Index.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition conjugacy_relation :=
  EquivRel (@mutually_subconjugate S F)
    (@mutually_subconjugate_refl S F) (@mutually_subconjugate_sym S F)
    (@mutually_subconjugate_trans S F).

Definition index_object := {eq_quot conjugacy_relation}.
#[export] HB.instance Definition _ := [Finite of index_object by <:%/].

Definition chain_class (c : chain F) : index_object := \pi_index_object c.

Lemma class_eq_mutual (c d : chain F) :
  reflect (chain_class c = chain_class d) (mutually_subconjugate c d).
Proof. exact: eqmodP. Qed.

Theorem class_eq_conjugate (c d : chain F) :
  reflect (chain_class c = chain_class d) (DPNormalizerChainConjugacy.conjugate c d).
Proof. rewrite DPNormalizerChainConjugacy.conjugate_iff_mutual; exact: class_eq_mutual. Qed.

Lemma representative_mutual (c : chain F) :
  mutually_subconjugate (repr (chain_class c)) c.
Proof. apply/class_eq_mutual; exact: reprK. Qed.

Definition index_relation (a b : index_object) := subconjugate (repr a) (repr b).

Theorem class_relation (c d : chain F) :
  index_relation (chain_class c) (chain_class d) = subconjugate c d.
Proof.
exact: subconjugate_congr (representative_mutual c) (representative_mutual d).
Qed.

Lemma index_relation_refl : reflexive index_relation.
Proof. move=> a; exact: subconjugate_refl. Qed.

Lemma index_relation_trans : transitive index_relation.
Proof. move=> a b c; exact: subconjugate_trans. Qed.

Theorem index_relation_antisymmetric (a b : index_object) :
  index_relation a b -> index_relation b a -> a = b.
Proof.
move=> hab hba.
have hm : mutually_subconjugate (repr a) (repr b) by apply/andP; split.
have he := elimT (class_eq_mutual _ _) hm.
by rewrite /chain_class !reprK in he.
Qed.

Definition index_hom (a b : index_object) : finType :=
  [the finType of {u : (Datatypes.unit : Type) | index_relation a b}].

Definition hom_of_relation (a b : index_object) (h : index_relation a b) : index_hom a b := Sub tt h.

Lemma hom_relation (a b : index_object) (f : index_hom a b) : index_relation a b.
Proof. exact (valP f). Qed.

Lemma index_hom_unique (a b : index_object) (f g : index_hom a b) : f = g.
Proof. apply val_inj; case: (val f); case: (val g); reflexivity. Qed.

Definition index_identity a : index_hom a a := hom_of_relation (index_relation_refl a).
Definition index_compose a b c (f : index_hom a b) (g : index_hom b c) : index_hom a c :=
  hom_of_relation (index_relation_trans (hom_relation f) (hom_relation g)).

Definition finite_index_category : finite_category.
Proof.
refine (@Build_finite_category [the finType of index_object] index_hom
  index_identity index_compose _ _ _); intros; exact: index_hom_unique.
Defined.

Definition index_category : category := fc_category finite_index_category.

Definition index_length (a : index_object) := length (repr a).

Lemma index_length_class (c : chain F) : index_length (chain_class c) = length c.
Proof. exact: mutually_subconjugate_length (representative_mutual c). Qed.

Lemma index_length_arrow (a b : index_object) (f : index_hom a b) : index_length b <= index_length a.
Proof. exact: subconjugate_length (hom_relation f). Qed.

End Index.
End DPNormalizerChainIndex.
