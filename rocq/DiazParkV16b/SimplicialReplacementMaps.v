(** Actual functoriality of simplicial replacement in the diagram. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialSetYoneda CategoryNerve BisimplicialSet SimplicialReplacementTypes SimplicialReplacement.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda
  DPCategoryNerve DPBisimplicialSet DPSimplicialReplacementTypes DPSimplicialReplacement.

Module DPSimplicialReplacementMaps.
Section Maps.
Variable C : category.
Variables F G : functor C simplicial_category.
Variable a : nat_trans F G.

Definition replacement_map_at p q (x : replacement_cell F p q) : replacement_cell G p q :=
  match x with existT s z => existT _ s (component (component a (initial_object s)) q z) end.

Lemma replacement_map_vertical p q n (g : ordinal_map q n) (x : replacement_cell F p n) :
  replacement_map_at (replacement_vertical g x) = replacement_vertical g (replacement_map_at x).
Proof.
case: x=>s z; rewrite /replacement_map_at /replacement_vertical.
congr (existT _ _ _); exact: simplicial_map_naturality.
Qed.

Lemma replacement_map_horizontal p m (f : ordinal_map p m) q (x : replacement_cell F m q) :
  replacement_map_at (replacement_horizontal f x) = replacement_horizontal f (replacement_map_at x).
Proof.
case: x=>s z; rewrite /replacement_map_at /replacement_horizontal.
congr (existT _ _ _).
exact (f_equal (fun u : simplicial_map (fobj F (initial_object s))
  (fobj G (fobj s (f ord0))) => component u q z)
  (naturality a (initial_arrow s (f ord0)))).
Qed.

Definition replacement_map_column p :
  simplicial_map (replacement_column F p) (replacement_column G p).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (replacement_column F p) (replacement_column G p)
  (fun q => @replacement_map_at p q) _).
move=> q n g; apply type_morphism_ext=> x; exact: replacement_map_vertical.
Defined.

Definition replacement_map : bisimplicial_map (replacement F) (replacement G).
Proof.
refine (@Build_nat_trans (opposite simplex_category) simplicial_category
  (replacement F) (replacement G) replacement_map_column _).
move=> p m f; apply nat_trans_ext=> q; apply type_morphism_ext=> x.
exact: replacement_map_horizontal.
Defined.

Lemma replacement_map_formula p q (s : simplex (nerve C) p)
    (z : simplex (fobj F (initial_object s)) q) :
  bisimplex_component replacement_map p q (existT _ s z) =
  existT _ s (component (component a (initial_object s)) q z).
Proof. reflexivity. Qed.

End Maps.

Definition replacement_functor (C : category) :
  functor (functor_category C simplicial_category) bisimplicial_category.
Proof.
refine (@Build_functor (functor_category C simplicial_category) bisimplicial_category
  (fun F => replacement F) (fun F G a => replacement_map a) _ _).
- move=> F; apply nat_trans_ext=> p; apply nat_trans_ext=> q;
  apply type_morphism_ext=> [[s z]]; reflexivity.
- move=> F G H a b; apply nat_trans_ext=> p; apply nat_trans_ext=> q;
  apply type_morphism_ext=> [[s z]]; reflexivity.
Defined.
End DPSimplicialReplacementMaps.
