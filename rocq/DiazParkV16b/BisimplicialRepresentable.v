(** Concrete representable bisimplicial models with literal pairs of ordinal maps. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda BisimplicialSet.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPBisimplicialSet.

Module DPBisimplicialRepresentable.
Definition representable_row (m n p : nat) : simplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) type_category
  (fun q => (ordinal_map p m * ordinal_map q n)%type)
  (fun q r f x => (x.1, ordinal_map_compose f x.2)) _ _).
- move=> q; apply type_morphism_ext => x; case: x => a b; congr (_, _); apply ordinal_map_ext => i; reflexivity.
- move=> q r s f g; apply type_morphism_ext => x; case: x => a b; congr (_, _); apply ordinal_map_ext => i; reflexivity.
Defined.

Definition representable_horizontal m n p r (f : ordinal_map p r) :
  simplicial_map (representable_row m n r) (representable_row m n p).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (representable_row m n r) (representable_row m n p)
  (fun q x => (ordinal_map_compose f x.1, x.2)) _).
move=> q s g; apply type_morphism_ext => x; case: x => a b; reflexivity.
Defined.

Definition representable (m n : nat) : bisimplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) simplicial_category
  (representable_row m n) (fun p q f => representable_horizontal m n f) _ _).
- move=> p; apply nat_trans_ext => q; apply type_morphism_ext => x; case: x => a b.
  congr (_, _); apply ordinal_map_ext => i; reflexivity.
- move=> p q r f g; apply nat_trans_ext => s; apply type_morphism_ext => x; case: x => a b.
  congr (_, _); apply ordinal_map_ext => i; reflexivity.
Defined.

Lemma representable_map m n p q r s (f : ordinal_map p r) (g : ordinal_map q s)
  (a : ordinal_map r m) (b : ordinal_map s n) :
  bisimplex_map (representable m n) f g (a,b) =
  (ordinal_map_compose f a, ordinal_map_compose g b).
Proof. reflexivity. Qed.

Definition representable_generator m n : bisimplex (representable m n) m n :=
  (ordinal_map_identity m, ordinal_map_identity n).

Lemma representable_generator_map m n p q (a : ordinal_map p m) (b : ordinal_map q n) :
  bisimplex_map (representable m n) a b (representable_generator m n) = (a,b).
Proof.
rewrite /representable_generator representable_map.
congr (_, _); apply ordinal_map_ext => i; reflexivity.
Qed.
End DPBisimplicialRepresentable.

