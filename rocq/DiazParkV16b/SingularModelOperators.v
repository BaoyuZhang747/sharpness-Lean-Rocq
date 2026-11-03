(** Natural operators obtained by postcomposing a genuine chain in a standard simplex. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic SingularSet
  SimplicialSet SimplicialChains SimplicialChainsMaps SingularCohomology SingularChainMapsLaws ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPTopological DPTopologicalSimplex DPSingularSet
  DPSingularCohomology DPSingularChainMapsLaws DPChainComplex DPSimplicialChainMaps.
Local Open Scope ring_scope.

Module DPSingularModelOperators.
Section Models.
Variable Real : realType.
Variable R : pzRingType.

Definition model_operator n m
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m)
    (X : topologicalType) :
    {linear chain_term (singular_chains Real R X) n -> chain_term (singular_chains Real R X) m} :=
  free_lift (fun s : DPSimplicialSet.simplex (singular_set Real X) n =>
    chain_map_at (singular_chain_map Real R s) m a).

Lemma model_operator_basis n m
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m)
    (X : topologicalType) (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  model_operator a X (free_basis R s) = chain_map_at (singular_chain_map Real R s) m a.
Proof. exact: free_lift_basis. Qed.

Lemma model_operator_naturality n m
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m)
    (X Y : topologicalType) (f : hom topological_category X Y)
    (x : chain_term (singular_chains Real R X) n) :
  chain_map_at (singular_chain_map Real R f) m (model_operator a X x) =
    model_operator a Y (chain_map_at (singular_chain_map Real R f) n x).
Proof.
apply (free_lift_ext
  (g := (chain_map_at (singular_chain_map Real R f) m \o model_operator a X : {linear _ -> _}))
  (h := (model_operator a Y \o chain_map_at (singular_chain_map Real R f) n : {linear _ -> _}))).
move=> s; rewrite /= model_operator_basis.
change (chain_map_at (singular_chain_map Real R f) m
    (chain_map_at (singular_chain_map Real R s) m a) =
  model_operator a Y (map_at R (singular_map Real f) n (free_basis R s))).
rewrite map_at_basis model_operator_basis.
symmetry; exact: singular_chain_composition.
Qed.

Definition identity_simplex n : DPSimplicialSet.simplex (singular_set Real (simplex_space Real n)) n :=
  continuous_identity (simplex_space Real n).

Lemma model_operator_identity n m
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m) :
  model_operator a (simplex_space Real n) (free_basis R (identity_simplex n)) = a.
Proof. rewrite model_operator_basis; exact: singular_chain_identity. Qed.

Lemma singular_generator_model n (X : topologicalType)
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  chain_map_at (singular_chain_map Real R s) n (free_basis R (identity_simplex n)) = free_basis R s.
Proof.
change (map_at R (singular_map Real s) n (free_basis R (identity_simplex n)) = free_basis R s).
rewrite map_at_basis.
congr (free_basis R _); apply topological_hom_ext => x; reflexivity.
Qed.

End Models.
End DPSingularModelOperators.
