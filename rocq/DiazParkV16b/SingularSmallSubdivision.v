(** Actual subdivision and its homotopy restricted to every small-chain subcomplex. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex TopologicalCategory TopologicalSimplexBasic
  SingularSet SimplicialChains SimplicialChainsMaps SingularCohomology SingularSmallChains
  SingularModelOperators SingularSmallModelOperators SingularSubdivisionOperators
  SingularSubdivisionBoundary SingularSubdivisionHomotopyModels SingularSubdivisionHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPTopological DPTopologicalSimplex
  DPSingularSet DPSingularCohomology DPSingularSmallChains DPSingularModelOperators
  DPSingularSmallModelOperators DPSingularSubdivision DPSingularSubdivisionBoundary
  DPSingularSubdivisionHomotopyModels DPSingularSubdivisionHomotopy.
Local Open Scope ring_scope.

Module DPSingularSmallSubdivision.
Section Subdivision.
Variable Real : realType.
Variable R : pzRingType.

Definition subdivision_model_chain n : chain_term (singular_chains Real R (simplex_space Real n)) n :=
  subdivision_at Real R (simplex_space Real n) n (free_basis R (identity_simplex Real n)).

Lemma subdivision_model_operator n (X : topologicalType)
    (x : chain_term (singular_chains Real R X) n) :
  model_operator (subdivision_model_chain n) X x = subdivision_at Real R X n x.
Proof.
apply (free_lift_ext (g := model_operator (subdivision_model_chain n) X)
  (h := (subdivision_at Real R X n : {linear _ -> _}))).
move=> s; rewrite model_operator_basis /subdivision_model_chain.
have h := @subdivision_naturality Real R (simplex_space Real n) X s n
  (free_basis R (identity_simplex Real n)).
change (chain_map_at (singular_chain_map Real R s) n
  (subdivision_at Real R (simplex_space Real n) n (free_basis R (identity_simplex Real n))) =
  subdivision_at Real R X n
    (chain_map_at (singular_chain_map Real R s) n (free_basis R (identity_simplex Real n)))) in h.
by rewrite singular_generator_model in h.
Qed.

Variable X : topologicalType.
Variable I : Type.
Variable U : I -> X -> Prop.
Let SC := @small_chains Real X I U R.
Let C := singular_chains Real R X.
Let inc := @small_chain_inclusion Real X I U R.

Definition small_subdivision_at n : {linear chain_term SC n -> chain_term SC n} :=
  @small_model_operator Real R X I U n n (subdivision_model_chain n).

Lemma small_subdivision_inclusion n (x : chain_term SC n) :
  chain_map_at inc n (small_subdivision_at n x) =
    subdivision_at Real R X n (chain_map_at inc n x).
Proof. rewrite /small_subdivision_at small_model_operator_inclusion; exact: subdivision_model_operator. Qed.

Lemma small_subdivision_boundary n (x : chain_term SC n.+1) :
  chain_d SC n (small_subdivision_at n.+1 x) = small_subdivision_at n (chain_d SC n x).
Proof.
apply: (@small_chain_inclusion_injective Real X I U R n).
rewrite -chain_map_commutes !small_subdivision_inclusion.
change (@DPSimplicialChains.boundary R (singular_set Real X) n
  (subdivision_at Real R X n.+1 (chain_map_at inc n.+1 x)) =
  subdivision_at Real R X n (chain_map_at inc n (chain_d SC n x))).
rewrite subdivision_boundary; congr (subdivision_at Real R X n _); exact (@chain_map_commutes R SC C inc n x).
Qed.

Definition small_subdivision_chain_map : chain_map SC SC :=
  @ChainMap R SC SC small_subdivision_at small_subdivision_boundary.

Definition small_subdivision_homotopy_at n : {linear chain_term SC n -> chain_term SC n.+1} :=
  @small_model_operator Real R X I U n n.+1 (universal_homotopy_chain Real R n).

Lemma small_subdivision_homotopy_inclusion n (x : chain_term SC n) :
  chain_map_at inc n.+1 (small_subdivision_homotopy_at n x) =
    subdivision_homotopy_at Real R n X (chain_map_at inc n x).
Proof. exact: small_model_operator_inclusion. Qed.

Definition small_subdivision_homotopy :
    chain_homotopy small_subdivision_chain_map (chain_identity SC).
Proof.
refine (@ChainHomotopy R SC SC _ _ small_subdivision_homotopy_at _ _).
- move=> x; apply: (@small_chain_inclusion_injective Real X I U R 0).
  change (chain_map_at inc 0 (chain_d SC 0 (small_subdivision_homotopy_at 0 x)) =
    chain_map_at inc 0 (small_subdivision_at 0 x - x)).
  rewrite linearB -chain_map_commutes small_subdivision_homotopy_inclusion small_subdivision_inclusion.
  exact: (chain_homotopy_zero (subdivision_homotopy Real R X)).
- move=> n x; apply: (@small_chain_inclusion_injective Real X I U R n.+1).
  change (chain_map_at inc n.+1
    (chain_d SC n.+1 (small_subdivision_homotopy_at n.+1 x) +
     small_subdivision_homotopy_at n (chain_d SC n x)) =
    chain_map_at inc n.+1 (small_subdivision_at n.+1 x - x)).
  rewrite linearD linearB -chain_map_commutes !small_subdivision_homotopy_inclusion
    small_subdivision_inclusion -chain_map_commutes.
  exact: (chain_homotopy_succ (subdivision_homotopy Real R X)).
Defined.

End Subdivision.
End DPSingularSmallSubdivision.


