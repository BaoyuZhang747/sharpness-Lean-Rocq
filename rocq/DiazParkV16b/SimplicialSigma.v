(** Genuine disjoint simplicial families, including empty and infinite families. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda SimplicialReplacementConstants.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPSimplicialReplacementConstants.
Module DPSimplicialSigma.
Definition sigma_set (I : Type) (X : I -> simplicial_set) : simplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) type_category
 (fun n=>{i : I & simplex (X i) n})
 (fun n m f x=>match x with existT i a=>existT _ i (simplex_map (X i) f a) end) _ _).
- move=>n; apply type_morphism_ext=>[[i a]]; by rewrite simplex_map_identity.
- move=>n m k f g; apply type_morphism_ext=>[[i a]]; by rewrite simplex_map_compose.
Defined.
Definition sigma_inclusion I (X:I->simplicial_set) i : simplicial_map (X i) (sigma_set X).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (X i) (sigma_set X)
 (fun n a=>existT _ i a) _); reflexivity.
Defined.
Definition sigma_map I (X Y:I->simplicial_set) (a:forall i,simplicial_map (X i) (Y i)) : simplicial_map (sigma_set X) (sigma_set Y).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (sigma_set X) (sigma_set Y)
 (fun n x=>match x with existT i b=>existT _ i (component (a i) n b) end) _).
move=>n m f; apply type_morphism_ext=>[[i b]]; by rewrite /= simplicial_map_naturality.
Defined.
Definition sigma_desc I (X:I->simplicial_set) Y (a:forall i,simplicial_map (X i) Y) : simplicial_map (sigma_set X) Y.
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (sigma_set X) Y
 (fun n x=>match x with existT i b=>component (a i) n b end) _).
move=>n m f; apply type_morphism_ext=>[[i b]]; exact: simplicial_map_naturality.
Defined.
Definition sigma_projection I (X:I->simplicial_set) : simplicial_map (sigma_set X) (constant_simplicial I).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (sigma_set X) (constant_simplicial I)
 (fun n x=>projT1 x) _).
move=>n m f; apply type_morphism_ext=>[[i a]]; reflexivity.
Defined.
Lemma sigma_map_inclusion I (X Y:I->simplicial_set) (a:forall i,simplicial_map (X i) (Y i)) i :
 nat_comp (sigma_inclusion X i) (sigma_map a)=nat_comp (a i) (sigma_inclusion Y i).
Proof. apply nat_trans_ext=>n; reflexivity. Qed.
End DPSimplicialSigma.
