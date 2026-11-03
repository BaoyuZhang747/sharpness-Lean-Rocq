From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory TopologicalCategory
  TopologicalSimplexBasic TopologicalSimplexAffine TopologicalSimplexContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.

Module DPTopologicalSimplexOrdinal.
Import DPSimplexCategory DPTopological DPTopologicalSimplex
  DPTopologicalSimplexAffine DPTopologicalSimplexContinuity.

Definition topological_simplex_functor (Real : realType) :
    functor simplex_category topological_category.
Proof.
refine (@Build_functor simplex_category topological_category
  (simplex_space Real) (fun n m f => simplex_map Real f) _ _).
- move=> n; exact: simplex_map_identity.
- move=> n m k f g; apply: topological_hom_ext => x.
  symmetry; exact: pushforward_composition.
Defined.

Lemma topological_simplex_functor_map (Real : realType) n m
    (f : ordinal_map n m) (x : simplex Real n) :
  fmap (topological_simplex_functor Real) f x = pushforward f x.
Proof. reflexivity. Qed.

End DPTopologicalSimplexOrdinal.
