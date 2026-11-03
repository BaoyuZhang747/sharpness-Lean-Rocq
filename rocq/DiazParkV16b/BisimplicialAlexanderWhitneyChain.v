(** The actual front/back Alexander--Whitney chain map to the finite total complex. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplexCategory SimplexCategoryOperators
  SimplicialSet SimplicialSetOperators SimplicialChains SimplicialChainsMaps
  BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyOrdinals
  BisimplicialAlexanderWhitneyFaces BisimplicialAlexanderWhitneyBoundary
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplexCategory DPSimplexOperators
  DPSimplicialSet DPSimplicialOperators DPSimplicialChains DPSimplicialChainMaps
  DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyOrdinals
  DPAlexanderWhitneyFaces DPAlexanderWhitneyBoundary DPFirstQuadrantChain DPFirstQuadrantChainTotal.
Local Open Scope ring_scope.

Module DPAlexanderWhitneyChain.
Section Chain.
Variable R : pzRingType.
Variable X : bisimplicial_set.
Let K := bisimplicial_bicomplex R X.

Definition aw_degree n (a : chain_term (diagonal_chains R X) n) : total_term K n :=
  fun p q h => free_map R (aw_simplex X p q n h) a.
Arguments aw_degree n a : clear implicits.
Lemma aw_degree_linear n : linear (@aw_degree n).
Proof.
move=> r a b; apply functional_extensionality_dep => p;
  apply functional_extensionality_dep => q; apply functional_extensionality_dep => h.
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@aw_degree n) (@aw_degree_linear n).

Lemma aw_degree_basis p q n (h : Nat.add p q = n) (x : simplex (diagonal X) n) :
  aw_degree n (free_basis R x) p q h = free_basis R (aw_simplex X p q n h x).
Proof. exact: free_map_basis. Qed.

Lemma aw_boundary_image p q n (h : Nat.add p q = n) (x : simplex (diagonal X) n.+1) :
  free_map R (aw_simplex X p q n h) (@boundary R (diagonal X) n (free_basis R x)) =
  \sum_(i < n.+2) (-1)^+i *: free_basis R
    (aw_simplex X p q n h (face (diagonal X) (inord i) x)).
Proof.
rewrite /boundary linear_sum; apply eq_bigr => i _.
by rewrite linearZ /face_map !free_map_basis.
Qed.

Lemma horizontal_boundary_basis p q (x : bisimplex X p.+1 q) :
  @horizontal_d R X p q (free_basis R x) =
  \sum_(i < p.+2) (-1)^+i *: free_basis R (horizontal_map X (coface (inord i)) q x).
Proof.
rewrite /horizontal_d; apply eq_bigr => i _; by rewrite map_at_basis.
Qed.
Lemma vertical_boundary_basis p q (x : bisimplex X p q.+1) :
  @vertical_d R X p q (free_basis R x) =
  \sum_(i < q.+2) (-1)^+i *: free_basis R (face (fobj X p) (inord i) x).
Proof.
rewrite /vertical_d /boundary; apply eq_bigr => i _; by rewrite /face_map free_map_basis.
Qed.

Lemma aw_degree_commutes_basis n (x : simplex (diagonal X) n.+1) :
  chain_d (total_chains R X) n (aw_degree n.+1 (free_basis R x)) =
  aw_degree n (chain_d (diagonal_chains R X) n (free_basis R x)).
Proof.
apply functional_extensionality_dep => p;
  apply functional_extensionality_dep => q; apply functional_extensionality_dep => h.
change (@horizontal_d R X p q (free_map R (aw_simplex X p.+1 q n.+1 (horizontal_input h)) (free_basis R x)) +
  (-1)^+p *: @vertical_d R X p q (free_map R (aw_simplex X p q.+1 n.+1 (vertical_input h)) (free_basis R x)) =
  free_map R (aw_simplex X p q n h) (@boundary R (diagonal X) n (free_basis R x))).
have eh : horizontal_input h = successor_left h by apply Prop_irrelevance.
have ev : vertical_input h = successor_right h by apply Prop_irrelevance.
rewrite eh ev !free_map_basis horizontal_boundary_basis vertical_boundary_basis aw_boundary_image.
symmetry; exact: aw_boundary.
Qed.

Theorem aw_degree_commutes n (a : chain_term (diagonal_chains R X) n.+1) :
  chain_d (total_chains R X) n (aw_degree n.+1 a) =
  aw_degree n (chain_d (diagonal_chains R X) n a).
Proof.
rewrite -[a](free_basis_generation a).
rewrite (linear_sum (chain_d (diagonal_chains R X) n)).
rewrite (linear_sum (@aw_degree n.+1 : {linear _ -> _}))
  (linear_sum (@aw_degree n : {linear _ -> _})) (linear_sum (chain_d (total_chains R X) n)).
apply eq_bigr => x _.
rewrite (linearZZ (chain_d (diagonal_chains R X) n)).
rewrite (linearZZ (@aw_degree n.+1 : {linear _ -> _}))
  (linearZZ (@aw_degree n : {linear _ -> _})) (linearZZ (chain_d (total_chains R X) n)).
by rewrite aw_degree_commutes_basis.
Qed.

Definition alexander_whitney : chain_map (diagonal_chains R X) (total_chains R X) :=
  @ChainMap R (diagonal_chains R X) (total_chains R X)
    (fun n => (@aw_degree n : {linear _ -> _})) aw_degree_commutes.

Theorem alexander_whitney_component p q n (h : Nat.add p q = n)
  (x : simplex (diagonal X) n) :
  chain_map_at alexander_whitney n (free_basis R x) p q h =
  free_basis R (aw_simplex X p q n h x).
Proof. exact: aw_degree_basis. Qed.
End Chain.
End DPAlexanderWhitneyChain.



