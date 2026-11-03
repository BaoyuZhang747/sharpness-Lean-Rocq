(** Actual small singular simplices for an arbitrary family of subsets. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic
  SingularSet SimplicialSet SimplicialSubcomplex SimplicialChains SimplicialChainsMaps
  ChainComplex FreeModuleEmbeddings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalSimplex DPSingularSet DPSimplicialSet
  DPSimplicialSubcomplex DPSimplicialChains DPSimplicialChainMaps DPChainComplex
  DPFreeModuleEmbeddings.

Module DPSingularSmallChains.
Section Small.
Variable Real : realType.
Variable X : topologicalType.
Variable I : Type.
Variable U : I -> X -> Prop.

Definition small_subcomplex : subcomplex (singular_set Real X).
Proof.
refine (@Subcomplex (singular_set Real X) (fun n s => exists i, forall t, U i (s t)) _).
move=> n m f s [i hi]; exists i; move=> t; exact: hi.
Defined.

Lemma small_simplex_refinement (J : Type) (V : J -> X -> Prop)
    (h : forall i, exists j, forall x, U i x -> V j x) n
    (s : simplex (singular_set Real X) n) :
  member small_subcomplex n s -> exists j, forall t, V j (s t).
Proof. move=> [i hi]; have [j hj] := h i; exists j => t; exact: hj (hi t). Qed.

Lemma small_cover_zero (h : forall x, exists i, U i x)
    (s : simplex (singular_set Real X) 0%N) : member small_subcomplex 0%N s.
Proof.
have [i hi] := h (s (@vertex Real 0%N ord0)); exists i => t.
have e : t = @vertex Real 0%N ord0 := simplex_zero_unique t _.
by rewrite e.
Qed.

Definition small_chains (R : pzRingType) := chains R (subcomplex_set small_subcomplex).
Definition small_chain_inclusion (R : pzRingType) :=
  chain_map_of R (subcomplex_inclusion small_subcomplex).

Theorem small_chain_inclusion_injective (R : pzRingType) n :
  injective (chain_map_at (small_chain_inclusion R) n).
Proof.
apply free_map_injective; exact: subcomplex_inclusion_injective.
Qed.
End Small.
End DPSingularSmallChains.
