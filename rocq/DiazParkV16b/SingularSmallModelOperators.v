(** Universal simplex operators preserve every family of small singular chains. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex TopologicalCategory TopologicalSimplexBasic
  SingularSet SimplicialSet SimplicialSubcomplex SimplicialChains SimplicialChainsMaps
  SingularCohomology SingularSmallChains SingularModelOperators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPTopological DPTopologicalSimplex
  DPSingularSet DPSingularCohomology DPSingularSmallChains DPSingularModelOperators
  DPSimplicialSubcomplex DPSimplicialChainMaps.
Local Open Scope ring_scope.

Module DPSingularSmallModelOperators.
Section SmallModels.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variable I : Type.
Variable U : I -> X -> Prop.
Let S := @small_subcomplex Real X I U.
Let SC := @small_chains Real X I U R.
Let inc := @small_chain_inclusion Real X I U R.

Definition small_model_simplex n m (s : subcomplex_simplex S n)
    (t : DPSimplicialSet.simplex (singular_set Real (simplex_space Real n)) m) :
    subcomplex_simplex S m.
Proof.
refine (exist _ (continuous_compose t (proj1_sig s)) _).
case: (proj2_sig s) => i hi; exists i => x; exact: hi.
Defined.

Definition small_model_push n m (s : subcomplex_simplex S n) :
    {linear chain_term (singular_chains Real R (simplex_space Real n)) m -> chain_term SC m} :=
  free_map R (@small_model_simplex n m s).
Arguments small_model_push {n m} s.

Lemma small_inclusion_basis n (s : subcomplex_simplex S n) :
  chain_map_at inc n (free_basis R s) = free_basis R (proj1_sig s).
Proof. exact: free_map_basis. Qed.

Lemma small_model_push_basis n m (s : subcomplex_simplex S n)
    (t : DPSimplicialSet.simplex (singular_set Real (simplex_space Real n)) m) :
  small_model_push s (free_basis R t) = free_basis R (small_model_simplex s t).
Proof. exact: free_map_basis. Qed.

Lemma small_model_push_inclusion n m (s : subcomplex_simplex S n)
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m) :
  chain_map_at inc m (small_model_push s a) =
    chain_map_at (singular_chain_map Real R (proj1_sig s)) m a.
Proof.
apply (free_lift_ext
  (g := (chain_map_at inc m \o small_model_push s : {linear _ -> _}))
  (h := chain_map_at (singular_chain_map Real R (proj1_sig s)) m)).
move=> t; rewrite /= small_model_push_basis small_inclusion_basis.
change (free_basis R (proj1_sig (small_model_simplex s t)) =
  map_at R (singular_map Real (proj1_sig s)) m (free_basis R t)).
rewrite map_at_basis; reflexivity.
Qed.

Definition small_model_operator n m
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m) :
    {linear chain_term SC n -> chain_term SC m} :=
  free_lift (fun s : subcomplex_simplex S n => small_model_push s a).

Lemma small_model_operator_basis n m
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m)
    (s : subcomplex_simplex S n) :
  small_model_operator a (free_basis R s) = small_model_push s a.
Proof. exact: free_lift_basis. Qed.

Theorem small_model_operator_inclusion n m
    (a : chain_term (singular_chains Real R (simplex_space Real n)) m)
    (x : chain_term SC n) :
  chain_map_at inc m (small_model_operator a x) =
    model_operator a X (chain_map_at inc n x).
Proof.
apply (free_lift_ext
  (g := (chain_map_at inc m \o small_model_operator a : {linear _ -> _}))
  (h := (model_operator a X \o chain_map_at inc n : {linear _ -> _}))).
move=> s; rewrite /= small_model_operator_basis small_inclusion_basis model_operator_basis.
exact: small_model_push_inclusion.
Qed.

End SmallModels.
End DPSingularSmallModelOperators.
