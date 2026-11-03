(** The actual all-ordinal bisimplicial replacement of a covariant
    simplicial-set diagram. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialSetYoneda CategoryNerve BisimplicialSet SimplicialReplacementTypes.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda
  DPCategoryNerve DPBisimplicialSet DPSimplicialReplacementTypes.

Module DPSimplicialReplacement.
Section Replacement.
Variable C : category.
Variable F : functor C simplicial_category.

Definition replacement_column (p : nat) : simplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) type_category
  (fun q => replacement_cell F p q)
  (fun q n g => replacement_vertical g) _ _).
- move=> q; apply type_morphism_ext=> x; exact: replacement_vertical_identity.
- move=> q n k g h; apply type_morphism_ext=> x; exact: replacement_vertical_compose.
Defined.

Definition replacement_horizontal_map p m (f : ordinal_map p m) :
  simplicial_map (replacement_column m) (replacement_column p).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (replacement_column m) (replacement_column p)
  (fun q => @replacement_horizontal C F p m f q) _).
move=> q n g; apply type_morphism_ext=> x; exact: replacement_mixed.
Defined.

Definition replacement : bisimplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) simplicial_category replacement_column
  (fun p m f => replacement_horizontal_map f) _ _).
- move=> p; apply nat_trans_ext=> q; apply type_morphism_ext=> x.
  exact: replacement_horizontal_identity.
- move=> p m k f g; apply nat_trans_ext=> q; apply type_morphism_ext=> x.
  exact: replacement_horizontal_compose.
Defined.

Lemma replacement_bisimplex p q : bisimplex replacement p q = replacement_cell F p q.
Proof. reflexivity. Qed.

Lemma replacement_horizontal_formula p m (f : ordinal_map p m) q (x : replacement_cell F m q) :
  horizontal_map replacement f q x = @replacement_horizontal C F p m f q x.
Proof. reflexivity. Qed.

Lemma replacement_vertical_formula p q n (g : ordinal_map q n) (x : replacement_cell F p n) :
  simplex_map (fobj replacement p) g x = replacement_vertical g x.
Proof. reflexivity. Qed.

End Replacement.
End DPSimplicialReplacement.
