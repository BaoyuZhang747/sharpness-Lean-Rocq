(** Degree-zero augmentation exactness from an actual continuous contraction. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic TopologicalSimplexContraction SimplicialSet SimplicialChains
  SimplicialChainsMaps SingularSet SingularCohomology SingularChainHomotopy
  SingularChainMapsLaws ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPTopological DPTopologicalHomotopy
  DPTopologicalSimplex DPTopologicalSimplexContraction DPSimplicialSet
  DPSimplicialChains DPSimplicialChainMaps DPSingularSet DPSingularCohomology
  DPSingularChainHomotopy DPSingularChainMapsLaws DPChainComplex.
Local Open Scope ring_scope.

Module DPSingularAugmentationContractible.
Section Contractible.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variable x0 : X.
Let constant : continuousType X X := [the continuousType X X of (cst x0)].
Let constant_simplex : simplex (singular_set Real X) 0%N :=
  [the continuousType (simplex_space Real 0) X of (cst x0)].
Let K := singular_chains Real R X.
Let e := augmentation R (singular_set Real X).

Definition constant_section (r : R^o) : chain_term K 0%N :=
  (r : R) *: free_basis R constant_simplex.

Lemma constant_section_linear : linear constant_section.
Proof. move=> a x y; by rewrite /constant_section scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build R [the lmodType R of R^o]
  (chain_term K 0%N) _ constant_section constant_section_linear.

Lemma constant_chain_zero (a : chain_term K 0%N) :
  chain_map_at (singular_chain_map Real R constant) 0%N a =
    (e a : R) *: free_basis R constant_simplex.
Proof.
change (chain_map_at (singular_chain_map Real R constant) 0%N a = constant_section (e a)).
apply: (free_lift_ext (g := chain_map_at (singular_chain_map Real R constant) 0%N)
  (h := (constant_section \o e : {linear _ -> _}))).
move=> s.
change (map_at R (singular_map Real constant) 0%N (free_basis R s) =
  constant_section (augmentation R (singular_set Real X) (free_basis R s))).
rewrite augmentation_basis /constant_section scale1r.
change (map_at R (singular_map Real constant) 0%N (free_basis R s) =
  free_basis R constant_simplex).
rewrite map_at_basis. congr (free_basis R _).
apply: topological_hom_ext => t. reflexivity.
Qed.

Variable H : continuous_homotopy Real (continuous_identity X) constant.

Theorem contractible_augmentation_exact (a : chain_term K 0%N) :
  e a = 0 -> @boundary R K 0%N a.
Proof.
move=> ha.
pose h := singular_chain_homotopy R H.
have hh := chain_homotopy_zero h a.
rewrite constant_chain_zero ha scale0r singular_chain_identity sub0r in hh.
exists (- chain_homotopy_at h 0%N a).
by rewrite linearN hh opprK.
Qed.
End Contractible.

Theorem simplex_augmentation_exact (Real : realType) (R : pzRingType) d
  (a : chain_term (singular_chains Real R (simplex_space Real d)) 0%N) :
  augmentation R (singular_set Real (simplex_space Real d)) a = 0 ->
  @boundary R (singular_chains Real R (simplex_space Real d)) 0%N a.
Proof.
exact: (@contractible_augmentation_exact Real R (simplex_space Real d)
  (@vertex Real d ord0) (simplex_contraction (@vertex Real d ord0)) a).
Qed.
End DPSingularAugmentationContractible.
