(** Literal relative maps of chain-map pairs and their exact-sequence comparison. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainMapImage ChainSubcomplex ChainSubcomplexMaps ChainShortExact ChainExactComparison
  ChainQuasiIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps DPChainMapImage
  DPChainSubcomplex DPChainSubcomplexMaps DPChainShortExact DPChainExactComparison
  DPChainQuasiIsomorphism DiazParkHomologicalModuleIso.
Module DPChainRelativePairs.

Definition relative_short_exact (R : pzRingType) (A B : chain_complex R)
    (i : chain_map A B) (hi : forall n, injective (chain_map_at i n)) :
    chain_short_exact i (relative_projection i).
Proof.
constructor.
- exact hi.
- exact: relative_projection_annihilates.
- move=> n x hx; exact: (proj1 (@relative_sequence_exact R A B i n x) hx).
- exact: relative_projection_surjective.
Defined.

Section PairMap.
Variable R : pzRingType.
Variables A B A' B' : chain_complex R.
Variables (i : chain_map A B) (j : chain_map A' B').
Variables (u : chain_map A A') (v : chain_map B B').
Variable w : forall n x, chain_map_at v n (chain_map_at i n x) =
  chain_map_at j n (chain_map_at u n x).

Definition pair_map_preserves n x : subspace_at (image_subcomplex i) n x ->
  subspace_at (image_subcomplex j) n (chain_map_at v n x).
Proof. move=> [a <-]; exists (chain_map_at u n a); symmetry; exact: w. Defined.

Definition relative_pair_map : chain_map (relative_chain i) (relative_chain j) :=
  @relative_map R B B' v (image_subcomplex i) (image_subcomplex j) pair_map_preserves.

Lemma relative_pair_map_projection n x :
  chain_map_at relative_pair_map n (chain_map_at (relative_projection i) n x) =
    chain_map_at (relative_projection j) n (chain_map_at v n x).
Proof. exact: relative_map_projection. Qed.

Variables (hi : forall n, injective (chain_map_at i n))
  (hj : forall n, injective (chain_map_at j n)).
Variables (hu : quasi_isomorphism u) (hv : quasi_isomorphism v).

Definition relative_pair_homology_iso n : @isomorphism (module_category R)
    (homology (relative_chain i) n) (homology (relative_chain j) n) :=
  @comparison_iso R A B (relative_chain i) A' B' (relative_chain j)
    i (relative_projection i) j (relative_projection j)
    (relative_short_exact hi) (relative_short_exact hj) u v relative_pair_map w
    relative_pair_map_projection
    (fun n => proj1 (hu n)) (fun n => proj2 (hu n))
    (fun n => proj1 (hv n)) (fun n => proj2 (hv n)) n.

Lemma relative_pair_homology_iso_hom n q :
  module_hom_fun (iso_hom (relative_pair_homology_iso n)) q = homology_map relative_pair_map n q.
Proof. exact: comparison_iso_hom. Qed.

Theorem relative_pair_map_quasi_isomorphism : quasi_isomorphism relative_pair_map.
Proof.
move=> n; split.
- move=> x y hxy; apply: (module_iso_hom_injective (e := relative_pair_homology_iso n)).
  by rewrite !relative_pair_homology_iso_hom.
- move=> y; exists (module_hom_fun (iso_inv (relative_pair_homology_iso n)) y).
  rewrite -relative_pair_homology_iso_hom.
  exact (@module_iso_inv_hom_apply R _ _ (relative_pair_homology_iso n) y).
Qed.
End PairMap.
End DPChainRelativePairs.
