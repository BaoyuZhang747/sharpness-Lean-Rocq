From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism BarPaths.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators
  CategoryNerve SimplicialSet SimplicialSetOperators CategoryNervePathsPrefix
  CategoryNervePaths CategoryNervePathsFacesOrdinal.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryNervePathFaces.
Import DPSimplexCategory DPSimplexOperators DPCategoryNerve DPSimplicialSet
  DPSimplicialOperators DiazParkBarPaths DPCategoryNervePaths
  DPCategoryNervePathEquivalence DPCategoryNerveFaceOrdinal.

Section Faces.
Variable C : category.

Lemma nerve_path_face_zero n (F : functor (ordinal_category n.+1) C) :
  nerve_path (face (nerve C) ord0 F) = @path_face C n 0 (nerve_path F).
Proof.
  change (nerve_path (functor_comp (ordinal_functor (@coface n ord0)) F) =
    @path_face C n 0 (nerve_path F)).
  rewrite coface_zero_shift. reflexivity.
Qed.

Lemma prefix_reindex_edge_shift n (F : functor (ordinal_category n.+2) C) :
  prefix_reindex_edge (ordinal_shift n) F =
    compose (nerve_head_edge F) (nerve_head_edge (nerve_tail F)).
Proof.
  unfold prefix_reindex_edge, nerve_head_edge. cbn.
  rewrite <- fmap_compose. f_equal. cbn. apply Prop_irrelevance.
Qed.

Lemma prefix_reindex_edge_prefix n m (f : ordinal_map n m)
    (F : functor (ordinal_category m.+2) C) :
  prefix_reindex_edge (ordinal_prefix f) F = nerve_head_edge F.
Proof. reflexivity. Qed.

Lemma prefix_reindex_edge_positive n (i : 'I_n.+1)
    (F : functor (ordinal_category n.+2) C) :
  prefix_reindex_edge (positive_coface i) F = nerve_head_edge F.
Proof. reflexivity. Qed.

Lemma nerve_path_face_one n (F : functor (ordinal_category n.+2) C) :
  nerve_path (face (nerve C) (shift_vertex ord0) F) =
    @path_face C n.+1 1 (nerve_path F).
Proof.
  change (nerve_path (functor_comp (ordinal_functor
    (coface (@shift_vertex n.+1 ord0))) F) = @path_face C n.+1 1 (nerve_path F)).
  rewrite coface_successor_prefix coface_zero_shift nerve_path_prefix_reindex.
  rewrite prefix_reindex_edge_shift. reflexivity.
Qed.

Lemma nerve_path_face_dimension_zero (i : 'I_2)
    (F : functor (ordinal_category 1) C) :
  nerve_path (face (nerve C) i F) = @path_face C 0 (val i) (nerve_path F).
Proof.
  destruct i as [[|[|i]] hi].
  - replace (@Ordinal 2 0 hi) with (@ord0 1) by (apply val_inj; reflexivity).
    apply nerve_path_face_zero.
  - change (existT (fun x => @path_from C 0 x)
      (fobj F (coface (@Ordinal 2 1 hi) ord0)) tt =
      existT (fun x => @path_from C 0 x) (fobj F ord0) tt).
    have e : coface (@Ordinal 2 1 hi) ord0 = ord0 by (apply val_inj; reflexivity).
    rewrite e. reflexivity.
  - discriminate hi.
Qed.

Lemma nerve_path_face n (i : 'I_n.+2)
    (F : functor (ordinal_category n.+1) C) :
  nerve_path (face (nerve C) i F) = @path_face C n (val i) (nerve_path F).
Proof.
  revert i F. induction n as [|n IH]; intros i F.
  - apply nerve_path_face_dimension_zero.
  - destruct i as [[|[|i]] hi].
    + replace (@Ordinal n.+3 0 hi) with (@ord0 n.+2)
        by (apply val_inj; reflexivity).
      apply nerve_path_face_zero.
    + replace (@Ordinal n.+3 1 hi) with (@shift_vertex n.+1 (@ord0 n.+1))
        by (apply val_inj; reflexivity).
      apply nerve_path_face_one.
    + change (nerve_path (functor_comp (ordinal_functor
        (coface (shift_vertex (shift_vertex (@Ordinal n.+1 i hi))))) F) =
        @path_face C n.+1 i.+2 (nerve_path F)).
      rewrite coface_successor_prefix nerve_path_prefix_reindex.
      rewrite coface_successor_normalized prefix_reindex_edge_positive.
      have h := IH (shift_vertex (@Ordinal n.+1 i hi)) (nerve_tail F).
      change (nerve_path (functor_comp (ordinal_functor
        (coface (shift_vertex (@Ordinal n.+1 i hi)))) (nerve_tail F)) =
        @path_face C n i.+1 (nerve_path (nerve_tail F))) in h.
      rewrite coface_successor_normalized in h.
      change (existT (fun x => @path_from C n x) (fobj (nerve_tail F) ord0)
        (nerve_path_from (functor_comp (ordinal_functor
          (positive_coface (@Ordinal n.+1 i hi))) (nerve_tail F))) =
        existT _ (fobj (nerve_tail F) ord0)
          (@path_inner_face C n i (fobj (nerve_tail F) ord0)
            (nerve_path_from (nerve_tail F)))) in h.
      have hf := @existT_inj2 [the eqType of classicType C]
        (fun x => @path_from C n x) _ _ _ h.
      unfold path_cons.
      cbn [path_cons path_face path_remove_inner path_inner_face nerve_path nerve_path_from].
      f_equal. f_equal. f_equal. exact hf.
Qed.

Lemma path_nerve_face n (i : 'I_n.+2) (p : @path C n.+1) :
  path_nerve (@path_face C n (val i) p) = face (nerve C) i (path_nerve p).
Proof.
  apply nerve_path_injective.
  rewrite nerve_path_nerve nerve_path_face nerve_path_nerve. reflexivity.
Qed.

End Faces.
End DPCategoryNervePathFaces.
