(** Literal base and constant-diagram augmentations of actual simplicial
    replacement, and their induced diagonal maps. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialSetYoneda CategoryNerve BisimplicialSet SimplicialReplacementTypes
  SimplicialReplacement SimplicialReplacementMaps SimplicialReplacementConstants.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda
  DPCategoryNerve DPBisimplicialSet DPSimplicialReplacementTypes DPSimplicialReplacement
  DPSimplicialReplacementMaps DPSimplicialReplacementConstants.

Module DPSimplicialReplacementAugmentation.
Section Base.
Variable C : category.
Variable F : functor C simplicial_category.

Definition base_projection_column p :
  simplicial_map (replacement_column F p) (constant_simplicial (simplex (nerve C) p)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (replacement_column F p) (constant_simplicial (simplex (nerve C) p))
  (fun q x => projT1 x) _).
move=> q n g; apply type_morphism_ext=> [[s z]]; reflexivity.
Defined.

Definition base_projection : bisimplicial_map (replacement F) (vertical_constant (nerve C)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) simplicial_category
  (replacement F) (vertical_constant (nerve C)) base_projection_column _).
move=> p m f; apply nat_trans_ext=> q; apply type_morphism_ext=> [[s z]]; reflexivity.
Defined.

Lemma base_projection_formula p q (s : simplex (nerve C) p)
    (z : simplex (fobj F (initial_object s)) q) :
  bisimplex_component base_projection p q (existT _ s z) = s.
Proof. reflexivity. Qed.

Definition diagonal_base_projection : simplicial_map (diagonal (replacement F)) (nerve C) :=
  nat_comp (diagonal_map base_projection) (vertical_diagonal_map (nerve C)).

Lemma diagonal_base_projection_formula n (s : simplex (nerve C) n)
    (z : simplex (fobj F (initial_object s)) n) :
  component diagonal_base_projection n (existT _ s z) = s.
Proof. reflexivity. Qed.
End Base.

Section Constant.
Variable C : category.
Variable X : simplicial_set.
Local Notation F := (@constant_diagram C simplicial_category X).

Definition constant_projection_column p : simplicial_map (replacement_column F p) X.
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (replacement_column F p) X (fun q x => projT2 x) _).
move=> q n g; apply type_morphism_ext=> [[s z]]; reflexivity.
Defined.

Definition constant_projection : bisimplicial_map (replacement F) (horizontal_constant X).
Proof.
refine (@Build_nat_trans (opposite simplex_category) simplicial_category
  (replacement F) (horizontal_constant X) constant_projection_column _).
move=> p m f; apply nat_trans_ext=> q; apply type_morphism_ext=> [[s z]]; reflexivity.
Defined.

Lemma constant_projection_formula p q (s : simplex (nerve C) p) (z : simplex X q) :
  bisimplex_component constant_projection p q (existT _ s z) = z.
Proof. reflexivity. Qed.
End Constant.

Section Cocone.
Variable C : category.
Variable F : functor C simplicial_category.
Variable X : simplicial_set.
Variable a : nat_trans F (@constant_diagram C simplicial_category X).

Definition coefficient_augmentation : bisimplicial_map (replacement F) (horizontal_constant X) :=
  nat_comp (replacement_map a) (constant_projection C X).

Definition diagonal_coefficient_augmentation : simplicial_map (diagonal (replacement F)) X :=
  nat_comp (diagonal_map coefficient_augmentation) (horizontal_diagonal_map X).

Lemma coefficient_augmentation_formula p q (s : simplex (nerve C) p)
    (z : simplex (fobj F (initial_object s)) q) :
  bisimplex_component coefficient_augmentation p q (existT _ s z) =
  component (component a (initial_object s)) q z.
Proof. reflexivity. Qed.

Lemma diagonal_coefficient_augmentation_formula n (s : simplex (nerve C) n)
    (z : simplex (fobj F (initial_object s)) n) :
  component diagonal_coefficient_augmentation n (existT _ s z) =
  component (component a (initial_object s)) n z.
Proof. reflexivity. Qed.
End Cocone.

Lemma base_projection_naturality (C : category) (F G : functor C simplicial_category)
    (a : nat_trans F G) :
  nat_comp (replacement_map a) (base_projection G) = base_projection F.
Proof.
apply nat_trans_ext=> p; apply nat_trans_ext=> q;
apply type_morphism_ext=> [[s z]]; reflexivity.
Qed.

End DPSimplicialReplacementAugmentation.
