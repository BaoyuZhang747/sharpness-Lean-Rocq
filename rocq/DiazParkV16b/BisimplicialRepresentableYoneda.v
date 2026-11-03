(** The actual Yoneda correspondence for concrete bisimplicial models. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda
  BisimplicialSet BisimplicialRepresentable.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda
  DPBisimplicialSet DPBisimplicialRepresentable.

Module DPBisimplicialRepresentableYoneda.
Lemma pull_horizontal (X : bisimplicial_set) p q r m n
  (f : ordinal_map p r) (a : ordinal_map r m) (b : ordinal_map q n) (x : bisimplex X m n) :
  horizontal_map X f q (bisimplex_map X a b x) = bisimplex_map X (ordinal_map_compose f a) b x.
Proof.
rewrite -(@bisimplex_map_horizontal X p r f q) -bisimplex_map_compose.
congr (bisimplex_map X _ _ x); apply ordinal_map_ext => i; reflexivity.
Qed.
Lemma pull_vertical (X : bisimplicial_set) p q s m n
  (g : ordinal_map q s) (a : ordinal_map p m) (b : ordinal_map s n) (x : bisimplex X m n) :
  simplex_map (fobj X p) g (bisimplex_map X a b x) = bisimplex_map X a (ordinal_map_compose g b) x.
Proof.
rewrite -(@bisimplex_map_vertical X p q s g) -bisimplex_map_compose.
congr (bisimplex_map X _ _ x); apply ordinal_map_ext => i; reflexivity.
Qed.

Definition characteristic_row (X : bisimplicial_set) m n (x : bisimplex X m n) p :
  simplicial_map (representable_row m n p) (fobj X p).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (representable_row m n p) (fobj X p) (fun q ab => bisimplex_map X ab.1 ab.2 x) _).
move=> q r f; apply type_morphism_ext => ab; case: ab => a b.
symmetry; exact: pull_vertical.
Defined.

Definition characteristic (X : bisimplicial_set) m n (x : bisimplex X m n) :
  bisimplicial_map (representable m n) X.
Proof.
refine (@Build_nat_trans (opposite simplex_category) simplicial_category
  (representable m n) X (characteristic_row x) _).
move=> p r f; apply nat_trans_ext => q; apply type_morphism_ext => ab; case: ab => a b.
symmetry; exact: pull_horizontal.
Defined.
Arguments characteristic X {m n} x.

Definition evaluate (X : bisimplicial_set) m n (a : bisimplicial_map (representable m n) X) :
  bisimplex X m n := bisimplex_component a m n (representable_generator m n).
Arguments evaluate X {m n} a.

Lemma evaluate_characteristic (X : bisimplicial_set) m n (x : bisimplex X m n) :
  evaluate X (characteristic X x) = x.
Proof. exact: bisimplex_map_identity. Qed.

Lemma characteristic_evaluate (X : bisimplicial_set) m n (a : bisimplicial_map (representable m n) X) :
  characteristic X (evaluate X a) = a.
Proof.
apply nat_trans_ext => p; apply nat_trans_ext => q; apply type_morphism_ext => ab; case: ab => f g.
have h := @bisimplex_component_natural (representable m n) X a p q m n f g (representable_generator m n).
rewrite representable_generator_map in h; symmetry; exact h.
Qed.

Lemma characteristic_natural (X Y : bisimplicial_set) (a : bisimplicial_map X Y)
  m n (x : bisimplex X m n) :
  nat_comp (characteristic X x) a = characteristic Y (bisimplex_component a m n x).
Proof.
apply nat_trans_ext => p; apply nat_trans_ext => q; apply type_morphism_ext => ab; case: ab => f g.
exact: bisimplex_component_natural.
Qed.
End DPBisimplicialRepresentableYoneda.
