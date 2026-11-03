(** Actual bisimplicial sets, all-ordinal pullbacks, and their diagonal. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda.

Module DPBisimplicialSet.
Definition bisimplicial_set := functor (opposite simplex_category) simplicial_category.
Definition bisimplex (X : bisimplicial_set) (p q : nat) : Type := simplex (fobj X p) q.
Definition horizontal_map (X : bisimplicial_set) p m (f : ordinal_map p m) q :
  bisimplex X m q -> bisimplex X p q := component (fmap X f) q.
Arguments horizontal_map X {_ _} f q x.

Lemma horizontal_map_identity (X : bisimplicial_set) p q (x : bisimplex X p q) :
  horizontal_map X (ordinal_map_identity p) q x = x.
Proof. exact (f_equal (fun a : simplicial_map (fobj X p) (fobj X p) => component a q x) (fmap_id X p)). Qed.

Lemma horizontal_map_compose (X : bisimplicial_set) p m k
  (f : ordinal_map p m) (g : ordinal_map m k) q (x : bisimplex X k q) :
  horizontal_map X (ordinal_map_compose f g) q x =
  horizontal_map X f q (horizontal_map X g q x).
Proof. exact (f_equal (fun a : simplicial_map (fobj X k) (fobj X p) => component a q x) (fmap_compose X g f)). Qed.

Definition bisimplex_map (X : bisimplicial_set) p q m n
  (f : ordinal_map p m) (g : ordinal_map q n) (x : bisimplex X m n) : bisimplex X p q :=
  horizontal_map X f q (simplex_map (fobj X m) g x).
Arguments bisimplex_map X {_ _ _ _} f g x.

Lemma bisimplex_map_identity (X : bisimplicial_set) p q (x : bisimplex X p q) :
  bisimplex_map X (ordinal_map_identity p) (ordinal_map_identity q) x = x.
Proof. by rewrite /bisimplex_map simplex_map_identity horizontal_map_identity. Qed.

Lemma bisimplex_map_compose (X : bisimplicial_set) p q m n a b
  (f : ordinal_map p m) (g : ordinal_map q n)
  (f' : ordinal_map a p) (g' : ordinal_map b q) (x : bisimplex X m n) :
  bisimplex_map X (ordinal_map_compose f' f) (ordinal_map_compose g' g) x =
  bisimplex_map X f' g' (bisimplex_map X f g x).
Proof.
rewrite /bisimplex_map horizontal_map_compose simplex_map_compose.
congr (horizontal_map X f' b _).
exact: simplicial_map_naturality.
Qed.

Lemma bisimplex_map_horizontal (X : bisimplicial_set) p m (f : ordinal_map p m) q
  (x : bisimplex X m q) :
  bisimplex_map X f (ordinal_map_identity q) x = horizontal_map X f q x.
Proof. by rewrite /bisimplex_map simplex_map_identity. Qed.

Lemma bisimplex_map_vertical (X : bisimplicial_set) p q n (g : ordinal_map q n)
  (x : bisimplex X p n) :
  bisimplex_map X (ordinal_map_identity p) g x = simplex_map (fobj X p) g x.
Proof. exact: horizontal_map_identity. Qed.

Definition diagonal (X : bisimplicial_set) : simplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) type_category
  (fun n => bisimplex X n n) (fun n m f => bisimplex_map X f f) _ _).
- move=> n; apply type_morphism_ext => x; exact: bisimplex_map_identity.
- move=> n m k f g; apply type_morphism_ext => x; exact: bisimplex_map_compose.
Defined.

Definition bisimplicial_map (X Y : bisimplicial_set) := nat_trans X Y.
Definition bisimplex_component (X Y : bisimplicial_set) (a : bisimplicial_map X Y) p q :
  bisimplex X p q -> bisimplex Y p q := component (component a p) q.
Arguments bisimplex_component {_ _} a p q x.

Lemma bisimplex_component_natural (X Y : bisimplicial_set) (a : bisimplicial_map X Y)
  p q m n (f : ordinal_map p m) (g : ordinal_map q n) (x : bisimplex X m n) :
  bisimplex_component a p q (bisimplex_map X f g x) =
  bisimplex_map Y f g (bisimplex_component a m n x).
Proof.
have h := f_equal (fun b : simplicial_map (fobj X m) (fobj Y p) =>
  component b q (simplex_map (fobj X m) g x)) (naturality a f).
change (bisimplex_component a p q (horizontal_map X f q (simplex_map (fobj X m) g x)) =
  horizontal_map Y f q (component (component a m) q (simplex_map (fobj X m) g x))) in h.
rewrite (simplicial_map_naturality (component a m) g x) in h.
exact h.
Qed.

Definition diagonal_map (X Y : bisimplicial_set) (a : bisimplicial_map X Y) :
  simplicial_map (diagonal X) (diagonal Y).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (diagonal X) (diagonal Y)
  (fun n => bisimplex_component a n n) _).
move=> n m f; apply type_morphism_ext => x; exact: bisimplex_component_natural.
Defined.

Definition bisimplicial_category : category :=
  functor_category (opposite simplex_category) simplicial_category.

Definition diagonal_functor : functor bisimplicial_category simplicial_category.
Proof.
refine (@Build_functor bisimplicial_category simplicial_category diagonal
  (fun X Y a => diagonal_map a) _ _).
- move=> X; apply nat_trans_ext => n; apply type_morphism_ext => x; reflexivity.
- move=> X Y Z a b; apply nat_trans_ext => n; apply type_morphism_ext => x; reflexivity.
Defined.
End DPBisimplicialSet.
