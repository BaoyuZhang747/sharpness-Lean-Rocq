From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialCopower.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet.

(** The actual coproduct of copies of X indexed by an arbitrary type I. *)
Definition copower (I : Type) (X : simplicial_set) : simplicial_set.
Proof.
  refine (@Build_functor (opposite simplex_category) type_category
    (fun n => (I * simplex X n)%type)
    (fun n m f x => (fst x, simplex_map X f (snd x))) _ _).
  - intro n. apply type_morphism_ext. intros [i x]. cbn.
    rewrite simplex_map_identity. reflexivity.
  - intros n m k f g. apply type_morphism_ext. intros [i x]. cbn.
    rewrite simplex_map_compose. reflexivity.
Defined.

Definition copower_inclusion I X (i : I) : simplicial_map X (copower I X).
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category X (copower I X)
    (fun n x => (i,x)) _). intros n m f. reflexivity.
Defined.

Definition copower_desc I X Y (a : I -> simplicial_map X Y) :
    simplicial_map (copower I X) Y.
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category (copower I X) Y
    (fun n x => component (a (fst x)) n (snd x)) _).
  intros n m f. apply type_morphism_ext. intros [i x].
  exact (simplicial_map_naturality (a i) f x).
Defined.

Lemma copower_desc_fac I X Y (a : I -> simplicial_map X Y) i :
  nat_comp (@copower_inclusion I X i) (copower_desc a) = a i.
Proof. apply nat_trans_ext. intro n. reflexivity. Qed.

Lemma copower_desc_unique I X Y (a : I -> simplicial_map X Y)
    (b : simplicial_map (copower I X) Y)
    (hb : forall i, nat_comp (@copower_inclusion I X i) b = a i) :
  b = copower_desc a.
Proof.
  apply nat_trans_ext. intro n. apply type_morphism_ext. intros [i x].
  exact (f_equal (fun t : simplicial_map X Y => component t n x) (hb i)).
Qed.

Definition copower_map I X Y (a : simplicial_map X Y) :
    simplicial_map (copower I X) (copower I Y).
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category (copower I X) (copower I Y)
    (fun n x => (fst x, component a n (snd x))) _).
  intros n m f. apply type_morphism_ext. intros [i x]. cbn.
  f_equal. exact (simplicial_map_naturality a f x).
Defined.

End DPSimplicialCopower.
