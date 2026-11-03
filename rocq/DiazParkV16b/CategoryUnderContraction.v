(** The actual contraction of an under category to its identity-arrow object. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryComma CategoryStructured.
From DiazParkV16b Require Import SimplicialReplacementConstants.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialReplacementConstants.
Module DPCategoryUnderContraction.
Section Under.
Variable D : category.
Variable a : D.
Local Notation U := (structured_category (functor_id D) a).
Definition under_initial : U := structured_point (functor_id D) a (identity a).
Definition under_initial_arrow (x:U) : hom U under_initial x.
Proof.
refine (@structured_morphism D D (functor_id D) a under_initial x (structured_arrow x) _).
change (compose (identity a) (structured_arrow x)=structured_arrow x).
exact: compose_id_left.
Defined.
Definition under_initial_nat_trans : nat_trans (@constant_diagram U U under_initial) (functor_id U).
Proof.
refine (@Build_nat_trans U U (@constant_diagram U U under_initial) (functor_id U) under_initial_arrow _).
move=>x y f; apply costructured_hom_ext.
change (compose (identity a) (structured_arrow y)=compose (structured_arrow x) (structured_map f)).
rewrite compose_id_left; symmetry; exact: structured_commutes.
Defined.
End Under.
End DPCategoryUnderContraction.
