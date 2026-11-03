(** The constant-total projections compose with actual Alexander--Whitney to
    the literal diagonal identifications, and consequently have actual sections. *)
From Coq Require Import Arith.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplexCategory SimplicialSet
  SimplicialChains SimplicialChainsMaps BisimplicialSet BisimplicialChains
  SimplicialReplacementConstants BisimplicialConstantTotal
  BisimplicialAlexanderWhitneyOrdinals BisimplicialAlexanderWhitneyFaces
  BisimplicialAlexanderWhitneyChain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplexCategory DPSimplicialSet
  DPSimplicialChains DPSimplicialChainMaps DPBisimplicialSet DPBisimplicialChains
  DPSimplicialReplacementConstants DPBisimplicialConstantTotal DPAlexanderWhitneyOrdinals
  DPAlexanderWhitneyFaces DPAlexanderWhitneyChain.
Local Open Scope ring_scope.

Module DPBisimplicialConstantAlexanderWhitney.

Lemma front_zero n (h : Nat.add n 0 = n) : front n 0 n h = ordinal_map_identity n.
Proof. apply ordinal_map_ext=> i; apply val_inj; reflexivity. Qed.

Lemma back_zero n (h : Nat.add 0 n = n) : back 0 n n h = ordinal_map_identity n.
Proof. apply ordinal_map_ext=> i; apply val_inj; reflexivity. Qed.

Lemma vertical_aw_simplex (X : simplicial_set) n (h : Nat.add n 0 = n)
  (x : simplex (diagonal (vertical_constant X)) n) :
  aw_simplex (vertical_constant X) n 0 n h x = x.
Proof.
change (simplex_map X (front n 0 n h) x = x).
by rewrite front_zero simplex_map_identity.
Qed.

Lemma horizontal_aw_simplex (X : simplicial_set) n (h : Nat.add 0 n = n)
  (x : simplex (diagonal (horizontal_constant X)) n) :
  aw_simplex (horizontal_constant X) 0 n n h x = x.
Proof.
change (simplex_map X (back 0 n n h) x = x).
by rewrite back_zero simplex_map_identity.
Qed.

Section Chains.
Variable R : pzRingType.
Variable X : simplicial_set.

Theorem vertical_projection_after_aw n
  (a : chain_term (diagonal_chains R (vertical_constant X)) n) :
  chain_map_at (vertical_projection R X) n
    (chain_map_at (alexander_whitney R (vertical_constant X)) n a) =
  map_at R (vertical_diagonal_map X) n a.
Proof.
apply (free_lift_ext
  (g := (chain_map_at (vertical_projection R X) n \o
    chain_map_at (alexander_whitney R (vertical_constant X)) n : {linear _ -> _}))
  (h := map_at R (vertical_diagonal_map X) n)).
move=> x.
change (@aw_degree R (vertical_constant X) n (free_basis R x) n 0%N (Nat.add_0_r n) =
  map_at R (vertical_diagonal_map X) n (free_basis R x)).
by rewrite aw_degree_basis vertical_aw_simplex map_at_basis.
Qed.

Theorem horizontal_projection_after_aw n
  (a : chain_term (diagonal_chains R (horizontal_constant X)) n) :
  chain_map_at (horizontal_projection R X) n
    (chain_map_at (alexander_whitney R (horizontal_constant X)) n a) =
  map_at R (horizontal_diagonal_map X) n a.
Proof.
apply (free_lift_ext
  (g := (chain_map_at (horizontal_projection R X) n \o
    chain_map_at (alexander_whitney R (horizontal_constant X)) n : {linear _ -> _}))
  (h := map_at R (horizontal_diagonal_map X) n)).
move=> x.
change (@aw_degree R (horizontal_constant X) n (free_basis R x) 0%N n erefl =
  map_at R (horizontal_diagonal_map X) n (free_basis R x)).
by rewrite aw_degree_basis horizontal_aw_simplex map_at_basis.
Qed.

Definition vertical_section : chain_map (chains R X) (total_chains R (vertical_constant X)) :=
  chain_composition (chain_map_of R (vertical_diagonal_inverse X))
    (alexander_whitney R (vertical_constant X)).

Definition horizontal_section : chain_map (chains R X) (total_chains R (horizontal_constant X)) :=
  chain_composition (chain_map_of R (horizontal_diagonal_inverse X))
    (alexander_whitney R (horizontal_constant X)).

Theorem vertical_projection_section n (a : term R X n) :
  chain_map_at (vertical_projection R X) n (chain_map_at vertical_section n a) = a.
Proof.
change (chain_map_at (vertical_projection R X) n
  (chain_map_at (alexander_whitney R (vertical_constant X)) n
    (map_at R (vertical_diagonal_inverse X) n a)) = a).
rewrite vertical_projection_after_aw.
change (free_map R (@idfun (simplex X n)) (free_map R (@idfun (simplex X n)) a) = a).
by rewrite !free_map_identity.
Qed.

Theorem horizontal_projection_section n (a : term R X n) :
  chain_map_at (horizontal_projection R X) n (chain_map_at horizontal_section n a) = a.
Proof.
change (chain_map_at (horizontal_projection R X) n
  (chain_map_at (alexander_whitney R (horizontal_constant X)) n
    (map_at R (horizontal_diagonal_inverse X) n a)) = a).
rewrite horizontal_projection_after_aw.
change (free_map R (@idfun (simplex X n)) (free_map R (@idfun (simplex X n)) a) = a).
by rewrite !free_map_identity.
Qed.
End Chains.
End DPBisimplicialConstantAlexanderWhitney.
