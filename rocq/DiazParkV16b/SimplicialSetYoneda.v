From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialYoneda.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet.

Definition simplicial_category : category :=
  functor_category (opposite simplex_category) type_category.

Definition standard_simplex_functor : functor simplex_category simplicial_category.
Proof.
  refine (@Build_functor simplex_category simplicial_category standard_simplex
    (fun n m f => standard_simplex_map f) _ _).
  - intro n. apply nat_trans_ext. intro k. apply type_morphism_ext. intro f.
    apply ordinal_map_ext. intro i. reflexivity.
  - intros n m k f g. apply nat_trans_ext. intro l.
    apply type_morphism_ext. intro h. apply ordinal_map_ext. intro i. reflexivity.
Defined.

Definition characteristic_simplex (X : simplicial_set) n (x : simplex X n) :
  simplicial_map (standard_simplex n) X.
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (standard_simplex n) X (fun k f => simplex_map X f x) _).
  intros k l f. apply type_morphism_ext. intro g.
  apply simplex_map_compose.
Defined.

Arguments characteristic_simplex _ {_} _.

Definition evaluate_standard_simplex (X : simplicial_set) n
    (a : simplicial_map (standard_simplex n) X) : simplex X n :=
  component a n (ordinal_map_identity n).

Arguments evaluate_standard_simplex _ {_} _.

Lemma evaluate_characteristic (X : simplicial_set) n (x : simplex X n) :
  evaluate_standard_simplex X (characteristic_simplex X x) = x.
Proof. apply simplex_map_identity. Qed.

Lemma characteristic_evaluate_component (X : simplicial_set) n
    (a : simplicial_map (standard_simplex n) X) k (f : ordinal_map k n) :
  component (characteristic_simplex X (evaluate_standard_simplex X a)) k f =
    component a k f.
Proof.
  have h := simplicial_map_naturality a f (ordinal_map_identity n).
  have e : simplex_map (standard_simplex n) f (ordinal_map_identity n) = f.
  { apply ordinal_map_ext. intro i. reflexivity. }
  rewrite e in h. symmetry. exact h.
Qed.

Lemma characteristic_evaluate (X : simplicial_set) n
    (a : simplicial_map (standard_simplex n) X) :
  characteristic_simplex X (evaluate_standard_simplex X a) = a.
Proof.
  apply nat_trans_ext. intro k. apply type_morphism_ext. intro f.
  apply characteristic_evaluate_component.
Qed.

(** An actual Type-category isomorphism, with both inverse functions given. *)
Definition simplex_yoneda_iso (X : simplicial_set) (n : nat) :
  @isomorphism type_category (simplicial_map (standard_simplex n) X) (simplex X n).
Proof.
  refine (@Build_isomorphism type_category
    (simplicial_map (standard_simplex n) X) (simplex X n)
    (@evaluate_standard_simplex X n) (@characteristic_simplex X n) _ _).
  - apply type_morphism_ext. intro a. apply characteristic_evaluate.
  - apply type_morphism_ext. intro x. apply evaluate_characteristic.
Defined.

Lemma characteristic_simplex_map (X : simplicial_set) n m (f : ordinal_map n m)
    (x : simplex X m) :
  characteristic_simplex X (simplex_map X f x) =
    nat_comp (standard_simplex_map f) (characteristic_simplex X x).
Proof.
  apply nat_trans_ext. intro k. apply type_morphism_ext. intro g.
  symmetry. apply simplex_map_compose.
Qed.

Lemma characteristic_simplex_natural (X Y : simplicial_set)
    (a : simplicial_map X Y) n (x : simplex X n) :
  characteristic_simplex Y (component a n x) =
    nat_comp (characteristic_simplex X x) a.
Proof.
  apply nat_trans_ext. intro k. apply type_morphism_ext. intro f.
  symmetry. apply simplicial_map_naturality.
Qed.

End DPSimplicialYoneda.
