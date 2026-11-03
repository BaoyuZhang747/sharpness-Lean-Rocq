(** Relative comparison transported across actual neighborhood equivalences. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology SingularChainMapsLaws
  SingularChainComparison SingularRelativePairs SingularRelativeCovers SingularChainExcisionSubspaces
  ChainComplex ChainMapImage ChainQuasiIsomorphism ChainQuasiIsomorphismLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSingularChainMapsLaws DPSingularChainComparison
  DPSingularRelativePairs DPSingularRelativeCovers DPSingularChainExcisionSubspaces
  DPChainComplex DPChainMapImage DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws.
Local Open Scope classical_set_scope.
Module DPSingularRelativeNeighborhoods.
Section Neighborhoods.
Variable Real : realType.
Variable R : pzRingType.
Variables A B X Y : topologicalType.
Variables (i : continuousType A B) (j : continuousType X Y)
  (p : continuousType A X) (q : continuousType B Y).
Variable w : forall a, q (i a) = j (p a).
Variables (N : set B) (U : set Y).
Variable hN : forall b, N b -> U (q b).
Variables (a : continuousType A (subset_space N)) (x : continuousType X (subset_space U)).
Variables (ha : forall z, val (a z) = i z) (hx : forall z, val (x z) = j z).

Lemma source_neighborhood_square z : continuous_identity B (i z) = subset_inclusion N (a z).
Proof. symmetry; exact: ha. Qed.
Lemma target_neighborhood_square z : continuous_identity Y (j z) = subset_inclusion U (x z).
Proof. symmetry; exact: hx. Qed.

Definition source_neighborhood_relative := @singular_relative_map Real R A B (subset_space N) B
  i (subset_inclusion N) a (continuous_identity B) source_neighborhood_square.
Definition target_neighborhood_relative := @singular_relative_map Real R X Y (subset_space U) Y
  j (subset_inclusion U) x (continuous_identity Y) target_neighborhood_square.
Definition attachment_relative := @singular_relative_map Real R A B X Y i j p q w.
Definition neighborhood_relative := @cover_relative_map Real R B Y q N U hN.

Lemma neighborhood_relative_square n z :
  chain_map_at neighborhood_relative n (chain_map_at source_neighborhood_relative n z) =
    chain_map_at target_neighborhood_relative n (chain_map_at attachment_relative n z).
Proof.
have [b <-] := @relative_projection_surjective R _ _ (singular_chain_map Real R i) n z.
rewrite /source_neighborhood_relative /target_neighborhood_relative /attachment_relative
  /neighborhood_relative /cover_relative_map !singular_relative_map_projection !singular_chain_identity.
reflexivity.
Qed.

Theorem relative_attachment_quasi_isomorphism
    (hi : injective i) (hj : injective j)
    (hqa : quasi_isomorphism (singular_chain_map Real R a))
    (hqx : quasi_isomorphism (singular_chain_map Real R x))
    (hqu : quasi_isomorphism neighborhood_relative) :
    quasi_isomorphism attachment_relative.
Proof.
have hid (Z : topologicalType) : quasi_isomorphism (singular_chain_map Real R (continuous_identity Z)).
  apply: (@quasi_isomorphism_ext R _ _ (chain_identity _)); first by move=> n z; symmetry; exact: singular_chain_identity.
  exact: quasi_isomorphism_identity.
have hs : quasi_isomorphism source_neighborhood_relative.
  apply: singular_relative_map_quasi_isomorphism; [exact hi | exact: val_inj | exact hqa | exact: hid].
have ht : quasi_isomorphism target_neighborhood_relative.
  apply: singular_relative_map_quasi_isomorphism; [exact hj | exact: val_inj | exact hqx | exact: hid].
apply: (@quasi_isomorphism_cancel_second R _ _ _ attachment_relative target_neighborhood_relative ht).
apply: (@quasi_isomorphism_ext R _ _ (chain_composition source_neighborhood_relative neighborhood_relative)).
- exact: neighborhood_relative_square.
- exact: quasi_isomorphism_composition hs hqu.
Qed.
End Neighborhoods.
End DPSingularRelativeNeighborhoods.
