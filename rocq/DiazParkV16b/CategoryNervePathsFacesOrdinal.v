From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryReindex CategoryIsomorphism.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators
  CategoryNervePathsPrefix CategoryNervePathsSplitting CategoryNervePaths.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryNerveFaceOrdinal.
Import DPSimplexCategory DPSimplexOperators DPCategoryNervePaths
  DPCategoryNerveSplitting DPCategoryNervePathEquivalence.

Definition prefix_vertex n m (f : ordinal_map n m) (i : 'I_n.+2) : 'I_m.+2.
Proof.
  destruct i as [[|i] hi].
  - exact ord0.
  - exact (shift_vertex (f (@Ordinal n.+1 i hi))).
Defined.

Definition ordinal_prefix n m (f : ordinal_map n m) : ordinal_map n.+1 m.+1.
Proof.
  refine (@OrdinalMap n.+1 m.+1 (@prefix_vertex n m f) _).
  intros [[|i] hi] [[|j] hj] hij; try discriminate hij.
  - exact (leqnn 0).
  - exact (leq0n _).
  - cbn [prefix_vertex].
    destruct (f (@Ordinal n.+1 i hi)) as [k hk] eqn:ek.
    destruct (f (@Ordinal n.+1 j hj)) as [l hl] eqn:el.
    cbn [shift_vertex].
    have h := @ordinal_monotone n m f (@Ordinal n.+1 i hi)
      (@Ordinal n.+1 j hj) hij.
    rewrite ek el in h. exact h.
Defined.

Arguments ordinal_prefix {_ _} _.

Lemma coface_zero_shift n : @coface n ord0 = ordinal_shift n.
Proof.
  apply ordinal_map_ext. intros [i hi]. apply val_inj. reflexivity.
Qed.

Lemma coface_successor_prefix n (i : 'I_n.+2) :
  coface (shift_vertex i) = ordinal_prefix (coface i).
Proof.
  apply ordinal_map_ext. intros [[|j] hj]; destruct i as [i hi]; apply val_inj.
  - reflexivity.
  - change (coface_value i.+1 j.+1 = (coface_value i j).+1).
    unfold coface_value. cbn. destruct (Nat.leb i j); reflexivity.
Qed.

(** This presentation preserves vertex zero definitionally even in dimension
    zero, where a further prefix decomposition would have an empty domain. *)
Definition positive_coface_vertex n (i : 'I_n.+1) (j : 'I_n.+1) : 'I_n.+2.
Proof.
  destruct j as [[|j] hj].
  - exact ord0.
  - exact (coface (shift_vertex i) (@Ordinal n.+1 j.+1 hj)).
Defined.

Lemma positive_coface_vertex_eq n (i j : 'I_n.+1) :
  positive_coface_vertex i j = coface (shift_vertex i) j.
Proof.
  destruct j as [[|j] hj].
  - destruct i as [i hi]. apply val_inj. reflexivity.
  - reflexivity.
Qed.

Definition positive_coface n (i : 'I_n.+1) : ordinal_map n n.+1.
Proof.
  refine (@OrdinalMap n n.+1 (@positive_coface_vertex n i) _).
  intros j k hjk. rewrite !positive_coface_vertex_eq.
  exact (ordinal_monotone (coface (shift_vertex i)) hjk).
Defined.

Arguments positive_coface {_} _.

Lemma coface_successor_normalized n (i : 'I_n.+1) :
  coface (shift_vertex i) = positive_coface i.
Proof.
  apply ordinal_map_ext. intro j. symmetry. apply positive_coface_vertex_eq.
Qed.

Section Reindex.
Context (C : category) (n m : nat) (f : ordinal_map n m)
  (F : functor (ordinal_category m.+1) C).

Definition prefix_reindex_edge :
  hom C (fobj F ord0)
    (fobj (functor_comp (ordinal_functor f) (nerve_tail F)) ord0) :=
  @fmap (ordinal_category m.+1) C F ord0 (shift_vertex (f ord0)) (leq0n _).

Lemma prefix_reindex_object (i : ordinal_category n.+1) :
  fobj (functor_comp (ordinal_functor (ordinal_prefix f)) F) i =
    fobj (nerve_prefix (fobj F ord0)
      (functor_comp (ordinal_functor f) (nerve_tail F)) prefix_reindex_edge) i.
Proof. destruct i as [[|i] hi]; reflexivity. Defined.

Lemma nerve_prefix_reindex :
  functor_comp (ordinal_functor (ordinal_prefix f)) F =
    nerve_prefix (fobj F ord0)
      (functor_comp (ordinal_functor f) (nerve_tail F)) prefix_reindex_edge.
Proof.
  refine (@functor_ext_pointwise _ _ _ _ prefix_reindex_object _).
  intros [[|i] hi] [[|j] hj] h; try discriminate h; cbn.
  - match goal with |- fmap F ?k = _ =>
      replace k with (@identity (ordinal_category m.+1) ord0)
        by (cbn; apply Prop_irrelevance)
    end.
    apply fmap_id.
  - unfold prefix_reindex_edge. rewrite <- fmap_compose.
    f_equal. cbn. apply Prop_irrelevance.
  - f_equal. cbn. apply Prop_irrelevance.
Qed.

Lemma nerve_path_prefix_reindex :
  nerve_path (functor_comp (ordinal_functor (ordinal_prefix f)) F) =
    @path_cons C n (fobj F ord0)
      (nerve_path (functor_comp (ordinal_functor f) (nerve_tail F)))
      prefix_reindex_edge.
Proof. rewrite nerve_prefix_reindex. apply nerve_path_prefix. Qed.

End Reindex.
End DPCategoryNerveFaceOrdinal.
