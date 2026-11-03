From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryIsomorphism.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryNerve.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet.

(** The ordinary nerve N(C)_n = Fun([n],C), with every ordinal action
    given by precomposition. No face-only or asserted nerve interface is used. *)
Definition nerve (C : category) : simplicial_set.
Proof.
  refine (@Build_functor (opposite simplex_category) type_category
    (fun n => functor (ordinal_category n) C)
    (fun n m f X => functor_comp (ordinal_functor f) X) _ _).
  - intro n. apply type_morphism_ext. intro X.
    rewrite ordinal_functor_identity. apply functor_comp_id_left.
  - intros n m k f g. apply type_morphism_ext. intro X.
    change (functor_comp (ordinal_functor (ordinal_map_compose g f)) X =
      functor_comp (ordinal_functor g) (functor_comp (ordinal_functor f) X)).
    rewrite ordinal_functor_compose. apply functor_comp_assoc.
Defined.

Definition nerve_map {C D : category} (F : functor C D) :
    simplicial_map (nerve C) (nerve D).
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (nerve C) (nerve D) (fun n X => functor_comp X F) _).
  intros n m f. apply type_morphism_ext. intro X.
  apply functor_comp_assoc.
Defined.

Lemma nerve_map_apply {C D : category} (F : functor C D) n
    (X : simplex (nerve C) n) :
  component (nerve_map F) n X = functor_comp X F.
Proof. reflexivity. Qed.

Lemma nerve_ordinal_action (C : category) n m (f : ordinal_map n m)
    (X : simplex (nerve C) m) :
  simplex_map (nerve C) f X = functor_comp (ordinal_functor f) X.
Proof. reflexivity. Qed.

Lemma nerve_map_identity (C : category) n (X : simplex (nerve C) n) :
  component (nerve_map (functor_id C)) n X = X.
Proof. apply functor_comp_id_right. Qed.

Lemma nerve_map_compose {C D E : category}
    (F : functor C D) (G : functor D E) n (X : simplex (nerve C) n) :
  component (nerve_map (functor_comp F G)) n X =
    component (nerve_map G) n (component (nerve_map F) n X).
Proof. symmetry. apply functor_comp_assoc. Qed.

End DPCategoryNerve.
