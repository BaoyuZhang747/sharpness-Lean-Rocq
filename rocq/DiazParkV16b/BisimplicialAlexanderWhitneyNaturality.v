(** Actual bisimplicial chain maps and naturality of the front/back comparison. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialChains SimplicialChainsMaps BisimplicialSet BisimplicialChains
  BisimplicialAlexanderWhitneyFaces BisimplicialAlexanderWhitneyChain
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialTypes DPSimplexCategory
  DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPBisimplicialSet DPBisimplicialChains
  DPAlexanderWhitneyFaces DPAlexanderWhitneyChain DPFirstQuadrantChain DPFirstQuadrantChainTotal
  DPFirstQuadrantChainTotalMaps.
Local Open Scope ring_scope.

Module DPAlexanderWhitneyNaturality.
Definition horizontal_simplicial_map (X Y : bisimplicial_set) (a : bisimplicial_map X Y) (q : nat) :
  simplicial_map (horizontal_simplicial X q) (horizontal_simplicial Y q).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (horizontal_simplicial X q) (horizontal_simplicial Y q)
  (fun p => bisimplex_component a p q) _).
move=> p m f; apply type_morphism_ext => x.
exact (f_equal (fun b : simplicial_map (fobj X p) (fobj Y m) => component b q x) (naturality a f)).
Defined.

Section Naturality.
Variable R : pzRingType.
Variables X Y : bisimplicial_set.
Variable a : bisimplicial_map X Y.

Definition bisimplicial_chain_map_at p q : {linear bi_term R X p q -> bi_term R Y p q} :=
  free_map R (bisimplex_component a p q).

Lemma bisimplicial_chain_map_horizontal p q x :
  @horizontal_d R Y p q (bisimplicial_chain_map_at p.+1 q x) =
  bisimplicial_chain_map_at p q (@horizontal_d R X p q x).
Proof.
exact (@map_boundary R (horizontal_simplicial X q) (horizontal_simplicial Y q)
  (horizontal_simplicial_map a q) p x).
Qed.
Lemma bisimplicial_chain_map_vertical p q x :
  @vertical_d R Y p q (bisimplicial_chain_map_at p q.+1 x) =
  bisimplicial_chain_map_at p q (@vertical_d R X p q x).
Proof. exact (@map_boundary R (fobj X p) (fobj Y p) (component a p) q x). Qed.

Definition bisimplicial_chain_map : bicomplex_map (bisimplicial_bicomplex R X) (bisimplicial_bicomplex R Y) :=
  @BicomplexMap R (bisimplicial_bicomplex R X) (bisimplicial_bicomplex R Y)
    bisimplicial_chain_map_at bisimplicial_chain_map_horizontal bisimplicial_chain_map_vertical.
Definition diagonal_chains_map : chain_map (diagonal_chains R X) (diagonal_chains R Y) :=
  chain_map_of R (diagonal_map a).
Definition total_chains_map : chain_map (total_chains R X) (total_chains R Y) :=
  total_map bisimplicial_chain_map.

Lemma alexander_whitney_natural_basis n (s : simplex (diagonal X) n) :
  chain_map_at total_chains_map n (chain_map_at (alexander_whitney R X) n (free_basis R s)) =
  chain_map_at (alexander_whitney R Y) n (chain_map_at diagonal_chains_map n (free_basis R s)).
Proof.
apply functional_extensionality_dep => p;
  apply functional_extensionality_dep => q; apply functional_extensionality_dep => h.
change (free_map R (bisimplex_component a p q)
  (free_map R (aw_simplex X p q n h) (free_basis R s)) =
  free_map R (aw_simplex Y p q n h)
  (free_map R (component (diagonal_map a) n) (free_basis R s))).
rewrite !free_map_basis; congr (free_basis R _); exact: aw_simplex_natural.
Qed.

Theorem alexander_whitney_natural n (x : chain_term (diagonal_chains R X) n) :
  chain_map_at total_chains_map n (chain_map_at (alexander_whitney R X) n x) =
  chain_map_at (alexander_whitney R Y) n (chain_map_at diagonal_chains_map n x).
Proof.
rewrite -[x](free_basis_generation x).
rewrite (linear_sum (chain_map_at (alexander_whitney R X) n))
  (linear_sum (chain_map_at diagonal_chains_map n))
  (linear_sum (chain_map_at total_chains_map n))
  (linear_sum (chain_map_at (alexander_whitney R Y) n)).
apply eq_bigr => s _.
rewrite (linearZZ (chain_map_at (alexander_whitney R X) n))
  (linearZZ (chain_map_at diagonal_chains_map n))
  (linearZZ (chain_map_at total_chains_map n))
  (linearZZ (chain_map_at (alexander_whitney R Y) n)).
by rewrite alexander_whitney_natural_basis.
Qed.
End Naturality.
End DPAlexanderWhitneyNaturality.
