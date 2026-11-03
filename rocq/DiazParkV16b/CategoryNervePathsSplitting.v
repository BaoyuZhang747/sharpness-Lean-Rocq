From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryReindex CategoryIsomorphism.
From DiazParkV16b Require Import SimplexCategory CategoryNervePathsPrefix.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryNerveSplitting.
Import DPSimplexCategory DPCategoryNervePaths.

Lemma nerve_prefix_head (C : category) n (x : C)
    (T : functor (ordinal_category n) C) (a : hom C x (fobj T ord0)) :
  fobj (nerve_prefix x T a) ord0 = x.
Proof. reflexivity. Qed.

Lemma nerve_tail_prefix_object (C : category) n (x : C)
    (T : functor (ordinal_category n) C) (a : hom C x (fobj T ord0))
    (i : ordinal_category n) :
  fobj (nerve_tail (nerve_prefix x T a)) i = fobj T i.
Proof. destruct i as [i hi]. reflexivity. Defined.

Lemma nerve_tail_prefix (C : category) n (x : C)
    (T : functor (ordinal_category n) C) (a : hom C x (fobj T ord0)) :
  nerve_tail (nerve_prefix x T a) = T.
Proof.
  refine (@functor_ext_pointwise _ _ _ _
    (@nerve_tail_prefix_object C n x T a) _).
  intros [i hi] [j hj] h. cbn.
  reflexivity.
Qed.

Lemma nerve_prefix_edge (C : category) n (x : C)
    (T : functor (ordinal_category n) C) (a : hom C x (fobj T ord0)) :
  nerve_head_edge (nerve_prefix x T a) = a.
Proof.
  cbn. match goal with |- compose a (fmap T ?h) = _ =>
    replace h with (@identity (ordinal_category n) ord0)
      by (cbn; apply Prop_irrelevance)
  end.
  rewrite fmap_id. apply compose_id_right.
Qed.

Lemma nerve_prefix_split_object (C : category) n
    (F : functor (ordinal_category n.+1) C) (i : ordinal_category n.+1) :
  fobj (nerve_prefix (fobj F ord0) (nerve_tail F) (nerve_head_edge F)) i =
    fobj F i.
Proof.
  destruct i as [[|i] hi].
  - cbn. f_equal. apply val_inj. reflexivity.
  - reflexivity.
Defined.

Lemma nerve_prefix_split (C : category) n
    (F : functor (ordinal_category n.+1) C) :
  nerve_prefix (fobj F ord0) (nerve_tail F) (nerve_head_edge F) = F.
Proof.
  refine (@functor_ext_pointwise _ _ _ _
    (@nerve_prefix_split_object C n F) _).
  intros [[|i] hi] [[|j] hj] h; try discriminate h.
  - replace hi with (ltn0Sn n.+1) by apply Prop_irrelevance.
    replace hj with (ltn0Sn n.+1) by apply Prop_irrelevance.
    cbn. rewrite hom_transport_loop.
    replace h with (@identity (ordinal_category n.+1) ord0)
      by (cbn; apply Prop_irrelevance).
    symmetry. apply fmap_id.
  - replace hi with (ltn0Sn n.+1) by apply Prop_irrelevance.
    cbn. rewrite hom_transport_loop.
    unfold nerve_head_edge.
    rewrite <- fmap_compose. f_equal. cbn. apply Prop_irrelevance.
  - cbn. reflexivity.
Qed.

End DPCategoryNerveSplitting.
