(** Literal relative singular-chain maps of actual commuting continuous squares. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology SingularChainMapsLaws
  SingularChainComparison ChainComplex ChainMapImage ChainRelativePairs ChainQuasiIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSingularChainMapsLaws DPSingularChainComparison
  DPChainComplex DPChainMapImage DPChainRelativePairs DPChainQuasiIsomorphism.
Module DPSingularRelativePairs.
Section Pair.
Variable Real : realType.
Variable R : pzRingType.
Variables A B A' B' : topologicalType.
Variables (i : continuousType A B) (j : continuousType A' B')
  (u : continuousType A A') (v : continuousType B B').
Variable w : forall a, v (i a) = j (u a).

Lemma singular_pair_square n x :
  chain_map_at (singular_chain_map Real R v) n (chain_map_at (singular_chain_map Real R i) n x) =
    chain_map_at (singular_chain_map Real R j) n (chain_map_at (singular_chain_map Real R u) n x).
Proof.
rewrite -!singular_chain_composition.
have e : @compose topological_category _ _ _ i v = @compose topological_category _ _ _ u j.
  apply/continuousEP; exact w.
by rewrite e.
Qed.

Definition singular_relative_map := relative_pair_map singular_pair_square.

Lemma singular_relative_map_projection n x :
  chain_map_at singular_relative_map n
    (chain_map_at (relative_projection (singular_chain_map Real R i)) n x) =
  chain_map_at (relative_projection (singular_chain_map Real R j)) n
    (chain_map_at (singular_chain_map Real R v) n x).
Proof. exact: relative_pair_map_projection. Qed.

Theorem singular_relative_map_quasi_isomorphism
    (hi : injective i) (hj : injective j)
    (hu : quasi_isomorphism (singular_chain_map Real R u))
    (hv : quasi_isomorphism (singular_chain_map Real R v)) :
    quasi_isomorphism singular_relative_map.
Proof.
apply: relative_pair_map_quasi_isomorphism.
- exact: singular_chains_injective.
- exact: singular_chains_injective.
- exact hu.
- exact hv.
Qed.
End Pair.
End DPSingularRelativePairs.
