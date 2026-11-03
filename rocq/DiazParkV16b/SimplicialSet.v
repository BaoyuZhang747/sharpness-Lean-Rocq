From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryIsomorphism.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialSet.
Import DPSimplicialTypes DPSimplexCategory.

(** A simplicial set is the actual contravariant functor on all ordinal maps. *)
Definition simplicial_set :=
  functor (opposite simplex_category) type_category.

Definition simplex (X : simplicial_set) (n : nat) : Type := fobj X n.

Definition simplex_map (X : simplicial_set) n m (f : ordinal_map n m) :
    simplex X m -> simplex X n := fmap X f.

Arguments simplex_map _ {_ _} _ _.

Lemma simplex_map_identity (X : simplicial_set) n (x : simplex X n) :
  simplex_map X (ordinal_map_identity n) x = x.
Proof. exact (f_equal (fun f => f x) (fmap_id X n)). Qed.

Lemma simplex_map_compose (X : simplicial_set) n m k
    (f : ordinal_map n m) (g : ordinal_map m k) (x : simplex X k) :
  simplex_map X (ordinal_map_compose f g) x =
    simplex_map X f (simplex_map X g x).
Proof. exact (f_equal (fun h => h x) (fmap_compose X g f)). Qed.

Definition simplicial_map (X Y : simplicial_set) := nat_trans X Y.

Lemma simplicial_map_naturality (X Y : simplicial_set)
    (a : simplicial_map X Y) n m (f : ordinal_map n m) (x : simplex X m) :
  component a n (simplex_map X f x) = simplex_map Y f (component a m x).
Proof. exact (f_equal (fun h => h x) (naturality a f)). Qed.

(** The representable standard simplex. Its k-simplices are exactly [k]->[n]. *)
Definition standard_simplex (n : nat) : simplicial_set.
Proof.
  refine (@Build_functor (opposite simplex_category) type_category
    (fun k => ordinal_map k n)
    (fun k l f g => ordinal_map_compose f g) _ _).
  - intro k. apply type_morphism_ext. intro g. apply ordinal_map_ext.
    intro i. reflexivity.
  - intros k l m f g. apply type_morphism_ext. intro h.
    apply ordinal_map_ext. intro i. reflexivity.
Defined.

Definition standard_simplex_map n m (f : ordinal_map n m) :
    simplicial_map (standard_simplex n) (standard_simplex m).
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (standard_simplex n) (standard_simplex m)
    (fun k g => ordinal_map_compose g f) _).
  intros k l g. apply type_morphism_ext. intro h.
  apply ordinal_map_ext. intro i. reflexivity.
Defined.

Arguments standard_simplex_map {_ _} _.

Lemma standard_simplex_map_apply n m (f : ordinal_map n m) k
    (g : ordinal_map k n) :
  component (standard_simplex_map f) k g = ordinal_map_compose g f.
Proof. reflexivity. Qed.

End DPSimplicialSet.
