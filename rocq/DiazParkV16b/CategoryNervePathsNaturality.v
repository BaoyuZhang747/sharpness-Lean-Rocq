From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism BarPaths.
From DiazParkV16b Require Import SimplexCategory CategoryNerve SimplicialSet
  CategoryNervePathsPrefix CategoryNervePaths CategoryBarPullbackPaths.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryNervePathNaturality.
Import DPSimplexCategory DPCategoryNerve DPSimplicialSet DiazParkBarPaths
  DPCategoryNervePaths DPCategoryNervePathEquivalence DPCategoryBarPullback.

Section Naturality.
Context (C D : category) (G : functor C D).

Lemma nerve_path_from_postcompose n (F : functor (ordinal_category n) C) :
  nerve_path_from (functor_comp F G) =
    path_map_from G n (fobj F ord0) (nerve_path_from F).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [nerve_path_from path_map_from].
    change (existT (fun y => (hom D (fobj G (fobj F ord0)) y *
      @path_from D n y)%type)
      (fobj G (fobj (nerve_tail F) ord0))
      (fmap G (nerve_head_edge F), nerve_path_from (nerve_tail (functor_comp F G))) =
      existT _ (fobj G (fobj (nerve_tail F) ord0))
      (fmap G (nerve_head_edge F),
        path_map_from G n (fobj (nerve_tail F) ord0) (nerve_path_from (nerve_tail F)))).
    f_equal. f_equal. rewrite <- IH.
    have e := functor_comp_assoc (ordinal_functor (ordinal_shift n)) F G.
    have ep := f_equal (@nerve_path D n) e.
    symmetry.
    exact (@existT_inj2 [the eqType of classicType D]
      (fun x => @path_from D n x) _ _ _ ep).
Qed.

Lemma nerve_path_postcompose n (F : functor (ordinal_category n) C) :
  nerve_path (functor_comp F G) = path_map G n (nerve_path F).
Proof.
  unfold nerve_path. cbn [path_map].
  f_equal. apply nerve_path_from_postcompose.
Qed.

Lemma path_nerve_map n (p : @path C n) :
  path_nerve (path_map G n p) = functor_comp (path_nerve p) G.
Proof.
  apply nerve_path_injective.
  rewrite nerve_path_nerve nerve_path_postcompose nerve_path_nerve.
  reflexivity.
Qed.

End Naturality.
End DPCategoryNervePathNaturality.
