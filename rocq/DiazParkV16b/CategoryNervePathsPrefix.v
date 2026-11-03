From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryReindex CategoryIsomorphism.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryIdentities
  CategoryNerve SimplicialSet.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryNervePaths.
Import DPSimplexCategory DPSimplexIdentities DPSimplicialSet DPCategoryNerve.

Definition shift_vertex (n : nat) (i : 'I_n.+1) : 'I_n.+2.
Proof. destruct i as [i hi]. exact (@Ordinal n.+2 i.+1 hi). Defined.

Arguments shift_vertex {_} _.

Definition ordinal_shift (n : nat) : ordinal_map n n.+1.
Proof.
  refine (@OrdinalMap n n.+1 (@shift_vertex n) _).
  intros [i hi] [j hj] hij. exact hij.
Defined.

Definition nerve_tail (C : category) n (F : functor (ordinal_category n.+1) C) :
  functor (ordinal_category n) C :=
  functor_comp (ordinal_functor (ordinal_shift n)) F.

Arguments nerve_tail {_ _} _.

Definition nerve_head_edge (C : category) n
    (F : functor (ordinal_category n.+1) C) :
  hom C (fobj F ord0) (fobj (nerve_tail F) ord0) :=
  @fmap (ordinal_category n.+1) C F ord0 (shift_vertex ord0) (leq0n 1).

Arguments nerve_head_edge {_ _} _.

Section Prefix.
Context (C : category) (n : nat) (x : C)
  (T : functor (ordinal_category n) C).

Definition prefix_object (i : 'I_n.+2) : C.
Proof.
  destruct i as [[|i] hi].
  - exact x.
  - exact (fobj T (@Ordinal n.+1 i hi)).
Defined.

Variable a : hom C x (fobj T ord0).

Definition prefix_arrow (i j : 'I_n.+2) (hij : (i <= j)%N) :
    hom C (prefix_object i) (prefix_object j).
Proof.
  destruct i as [[|i] hi], j as [[|j] hj].
  - exact (identity x).
  - exact (compose a (@fmap (ordinal_category n) C T ord0
      (@Ordinal n.+1 j hj) (leq0n j))).
  - discriminate hij.
  - exact (@fmap (ordinal_category n) C T (@Ordinal n.+1 i hi)
      (@Ordinal n.+1 j hj) hij).
Defined.

Lemma prefix_arrow_identity (i : 'I_n.+2) :
  prefix_arrow (leqnn i) = identity (prefix_object i).
Proof.
  destruct i as [[|i] hi].
  - reflexivity.
  - cbn [prefix_arrow prefix_object].
    match goal with |- fmap T ?h = _ =>
      replace h with (@identity (ordinal_category n) (@Ordinal n.+1 i hi))
        by (cbn; apply Prop_irrelevance)
    end.
    apply fmap_id.
Qed.

Lemma prefix_arrow_compose (i j k : 'I_n.+2)
    (hij : (i <= j)%N) (hjk : (j <= k)%N) :
  prefix_arrow (leq_trans hij hjk) =
    compose (prefix_arrow hij) (prefix_arrow hjk).
Proof.
  destruct i as [[|i] hi], j as [[|j] hj], k as [[|k] hk];
    try discriminate hij; try discriminate hjk.
  - symmetry. apply compose_id_left.
  - symmetry. apply compose_id_left.
  - cbn. rewrite compose_assoc. f_equal.
    rewrite <- fmap_compose. f_equal. cbn. apply Prop_irrelevance.
  - cbn. rewrite <- fmap_compose. f_equal. cbn. apply Prop_irrelevance.
Qed.

Definition nerve_prefix : functor (ordinal_category n.+1) C.
Proof.
  refine (@Build_functor (ordinal_category n.+1) C prefix_object
    (@prefix_arrow) _ _).
  - exact prefix_arrow_identity.
  - exact prefix_arrow_compose.
Defined.

End Prefix.

Arguments nerve_prefix {_ _} _ _ _.

End DPCategoryNervePaths.
