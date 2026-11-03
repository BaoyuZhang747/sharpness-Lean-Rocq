(** Exact-sequence assembly of the actual realization unit over a commuting attachment square. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialChains SimplicialChainsMaps
  GeometricRealizationCarrier GeometricRealizationMaps RealizationUnitChains
  TopologicalCategory SingularCohomology SingularChainMapsLaws SingularChainComparison SingularRelativePairs
  FreeModuleEmbeddings ChainComplex ChainMapImage ChainRelativePairs ChainQuasiIsomorphism
  ChainQuasiIsomorphismLaws ChainExactMiddleComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPGeometricRealization DPGeometricRealizationMaps
  DPRealizationUnitChains DPTopological DPSingularCohomology DPSingularChainMapsLaws DPSingularChainComparison
  DPSingularRelativePairs DPFreeModuleEmbeddings DPChainComplex DPChainMapImage DPChainRelativePairs
  DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPChainExactMiddleComparison.
Module DPRealizationUnitAttachment.
Section Unit.
Variable Real : realType.
Variable R : pzRingType.

Lemma unit_pair_square (A B : simplicial_set) (i : simplicial_map A B) n x :
  chain_map_at (realization_unit_chains Real R B) n (chain_map_at (chain_map_of R i) n x) =
  chain_map_at (singular_chain_map Real R (realization_map Real i)) n
    (chain_map_at (realization_unit_chains Real R A) n x).
Proof. symmetry; exact: realization_unit_naturality. Qed.
Definition realization_relative_unit (A B : simplicial_set) (i : simplicial_map A B) :=
  relative_pair_map (@unit_pair_square A B i).

Lemma realization_relative_unit_projection (A B : simplicial_set) (i : simplicial_map A B) n x :
  chain_map_at (realization_relative_unit i) n (chain_map_at (relative_projection (chain_map_of R i)) n x) =
  chain_map_at (relative_projection (singular_chain_map Real R (realization_map Real i))) n
    (chain_map_at (realization_unit_chains Real R B) n x).
Proof. exact: relative_pair_map_projection. Qed.

Lemma realization_relative_unit_quasi_isomorphism (A B : simplicial_set) (i : simplicial_map A B)
    (hi : forall n, injective (component i n)) (hri : injective (realization_map Real i))
    (hA : quasi_isomorphism (realization_unit_chains Real R A))
    (hB : quasi_isomorphism (realization_unit_chains Real R B)) :
    quasi_isomorphism (realization_relative_unit i).
Proof.
apply: relative_pair_map_quasi_isomorphism.
- move=> n; exact: free_map_injective.
- move=> n; exact: singular_chains_injective.
- exact hA.
- exact hB.
Qed.

Variables A B X Y : simplicial_set.
Variables (i : simplicial_map A B) (p : simplicial_map A X)
  (q : simplicial_map B Y) (j : simplicial_map X Y).
Variable w : nat_comp i q = nat_comp p j.

Lemma simplicial_attachment_square n x :
  chain_map_at (chain_map_of R q) n (chain_map_at (chain_map_of R i) n x) =
  chain_map_at (chain_map_of R j) n (chain_map_at (chain_map_of R p) n x).
Proof. change (map_at R q n (map_at R i n x) = map_at R j n (map_at R p n x)); by rewrite -!map_composition w. Qed.
Definition simplicial_attachment_relative := relative_pair_map simplicial_attachment_square.

Lemma realized_attachment_square a : realization_map Real q (realization_map Real i a) =
  realization_map Real j (realization_map Real p a).
Proof.
have e : @compose topological_category _ _ _ (realization_map Real i) (realization_map Real q) =
    @compose topological_category _ _ _ (realization_map Real p) (realization_map Real j).
  by rewrite -!realization_map_composition w.
exact (congr1 (fun f : continuousType (realization_space Real A) (realization_space Real Y) => f a) e).
Qed.
Definition singular_attachment_relative := singular_relative_map Real R realized_attachment_square.

Lemma relative_unit_attachment_square n x :
  chain_map_at (realization_relative_unit j) n (chain_map_at simplicial_attachment_relative n x) =
  chain_map_at singular_attachment_relative n (chain_map_at (realization_relative_unit i) n x).
Proof.
have [b <-] := @relative_projection_surjective R _ _ (chain_map_of R i) n x.
rewrite /simplicial_attachment_relative relative_pair_map_projection !realization_relative_unit_projection
  /singular_attachment_relative
  (@singular_relative_map_projection Real R _ _ _ _ (realization_map Real i) (realization_map Real j)
    (realization_map Real p) (realization_map Real q) realized_attachment_square).
congr (chain_map_at (relative_projection (singular_chain_map Real R (realization_map Real j))) n _).
symmetry; exact: realization_unit_naturality.
Qed.

Theorem realization_unit_attachment_quasi_isomorphism
    (hi : forall n, injective (component i n)) (hj : forall n, injective (component j n))
    (hri : injective (realization_map Real i)) (hrj : injective (realization_map Real j))
    (hA : quasi_isomorphism (realization_unit_chains Real R A))
    (hB : quasi_isomorphism (realization_unit_chains Real R B))
    (hX : quasi_isomorphism (realization_unit_chains Real R X))
    (hs : quasi_isomorphism simplicial_attachment_relative)
    (ht : quasi_isomorphism singular_attachment_relative) :
    quasi_isomorphism (realization_unit_chains Real R Y).
Proof.
have hrel : quasi_isomorphism (realization_relative_unit j).
  apply: (@quasi_isomorphism_cancel_first R _ _ _ simplicial_attachment_relative (realization_relative_unit j) hs).
  apply: (@quasi_isomorphism_ext R _ _ (chain_composition (realization_relative_unit i) singular_attachment_relative)).
  - move=> n x; symmetry; exact: relative_unit_attachment_square.
  - apply: quasi_isomorphism_composition; last exact ht.
    exact: realization_relative_unit_quasi_isomorphism.
have hjc n : injective (chain_map_at (chain_map_of R j) n) by exact: free_map_injective.
have hrjc n : injective (chain_map_at (singular_chain_map Real R (realization_map Real j)) n)
  by exact: singular_chains_injective.
exact (@middle_quasi_isomorphism R _ _ _ _ _ _ (chain_map_of R j) (relative_projection (chain_map_of R j))
  (singular_chain_map Real R (realization_map Real j)) (relative_projection (singular_chain_map Real R (realization_map Real j)))
  (relative_short_exact hjc) (relative_short_exact hrjc)
  (realization_unit_chains Real R X) (realization_unit_chains Real R Y) (realization_relative_unit j)
  (@unit_pair_square X Y j) (@realization_relative_unit_projection X Y j) hX hrel).
Qed.
End Unit.
End DPRealizationUnitAttachment.
