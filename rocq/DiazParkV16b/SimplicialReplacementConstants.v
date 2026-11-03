(** Native constant simplicial and bisimplicial objects for literal replacement
    augmentations, with their actual diagonal identifications. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialSetYoneda BisimplicialSet.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPBisimplicialSet.

Module DPSimplicialReplacementConstants.

Definition constant_diagram (C D : category) (x : D) : functor C D.
Proof.
refine (@Build_functor C D (fun _ => x) (fun _ _ _ => identity x) _ _).
- reflexivity.
- intros; symmetry; exact: compose_id_left.
Defined.

Definition constant_simplicial (A : Type) : simplicial_set :=
  @constant_diagram (opposite simplex_category) type_category A.

Definition constant_simplicial_map (A B : Type) (u : A -> B) :
  simplicial_map (constant_simplicial A) (constant_simplicial B).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (constant_simplicial A) (constant_simplicial B) (fun _ => u) _); reflexivity.
Defined.

Definition constant_simplicial_functor : functor type_category simplicial_category.
Proof.
refine (@Build_functor type_category simplicial_category constant_simplicial
  (fun A B u => constant_simplicial_map u) _ _).
- intro A; apply nat_trans_ext=> n; reflexivity.
- intros; apply nat_trans_ext=> n; reflexivity.
Defined.

Definition vertical_constant (X : simplicial_set) : bisimplicial_set :=
  functor_comp X constant_simplicial_functor.

Definition horizontal_constant (X : simplicial_set) : bisimplicial_set :=
  @constant_diagram (opposite simplex_category) simplicial_category X.

Definition vertical_diagonal_map (X : simplicial_set) : simplicial_map (diagonal (vertical_constant X)) X.
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (diagonal (vertical_constant X)) X (fun _ x => x) _); reflexivity.
Defined.

Definition vertical_diagonal_inverse (X : simplicial_set) : simplicial_map X (diagonal (vertical_constant X)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  X (diagonal (vertical_constant X)) (fun _ x => x) _); reflexivity.
Defined.

Definition vertical_diagonal_iso (X : simplicial_set) :
  @isomorphism simplicial_category (diagonal (vertical_constant X)) X.
Proof.
refine (@Build_isomorphism simplicial_category _ _ (vertical_diagonal_map X)
  (vertical_diagonal_inverse X) _ _); apply nat_trans_ext=> n; reflexivity.
Defined.

Definition horizontal_diagonal_map (X : simplicial_set) : simplicial_map (diagonal (horizontal_constant X)) X.
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (diagonal (horizontal_constant X)) X (fun _ x => x) _); reflexivity.
Defined.

Definition horizontal_diagonal_inverse (X : simplicial_set) : simplicial_map X (diagonal (horizontal_constant X)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  X (diagonal (horizontal_constant X)) (fun _ x => x) _); reflexivity.
Defined.

Definition horizontal_diagonal_iso (X : simplicial_set) :
  @isomorphism simplicial_category (diagonal (horizontal_constant X)) X.
Proof.
refine (@Build_isomorphism simplicial_category _ _ (horizontal_diagonal_map X)
  (horizontal_diagonal_inverse X) _ _); apply nat_trans_ext=> n; reflexivity.
Defined.

End DPSimplicialReplacementConstants.
