(** The actual singular simplicial set of a MathComp topological space. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  TopologicalCategory TopologicalSimplexOrdinal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPTopological
  DPTopologicalSimplexOrdinal.

Module DPSingularSet.
Section Singular.
Variable Real : realType.
Let delta := topological_simplex_functor Real.

Definition singular_set (X : topologicalType) : simplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) type_category
  (fun n => hom topological_category (fobj delta n) X)
  (fun n m f s => compose (fmap delta f) s) _ _).
- move=> n; apply type_morphism_ext => s.
  by rewrite fmap_id compose_id_left.
- move=> n m k f g; apply type_morphism_ext => s.
  rewrite fmap_compose; exact: compose_assoc.
Defined.

Definition singular_map (X Y : topologicalType)
    (f : hom topological_category X Y) :
    simplicial_map (singular_set X) (singular_set Y).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (singular_set X) (singular_set Y) (fun n s => compose s f) _).
move=> n m g; apply type_morphism_ext => s; exact: compose_assoc.
Defined.

Lemma singular_map_at (X Y : topologicalType)
    (f : hom topological_category X Y) n (s : simplex (singular_set X) n) x :
  component (singular_map f) n s x = f (s x).
Proof. reflexivity. Qed.

Lemma singular_map_identity (X : topologicalType) n
    (s : simplex (singular_set X) n) :
  component (singular_map (@identity topological_category X)) n s = s.
Proof. exact: compose_id_right. Qed.

Lemma singular_map_composition (X Y Z : topologicalType)
    (f : hom topological_category X Y) (g : hom topological_category Y Z)
    n (s : simplex (singular_set X) n) :
  component (singular_map (compose f g)) n s =
    component (singular_map g) n (component (singular_map f) n s).
Proof. symmetry; exact: compose_assoc. Qed.
End Singular.
End DPSingularSet.
