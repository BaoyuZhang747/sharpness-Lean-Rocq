(** Actual iterated subdivision takes every finite singular chain into small chains. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category ModuleInfrastructure BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainIteration EventualSubmodule
  TopologicalCategory SimplicialSet SimplicialSubcomplex SimplicialChains SimplicialChainsMaps
  SingularSet SingularCohomology SingularSmallChains SingularSmallSubdivision
  SingularSubdivisionOperators SingularSubdivisionBoundary SingularSubdivisionSmallnessSingular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainIteration DPEventualSubmodule
  DPSimplicialSet DPSimplicialSubcomplex DPSimplicialChains DPSimplicialChainMaps
  DPSingularSet DPSingularCohomology DPSingularSmallChains DPSingularSmallSubdivision
  DPSingularSubdivision DPSingularSubdivisionBoundary DPSingularSubdivisionSmallnessSingular.
Local Open Scope ring_scope.

Module DPSingularSubdivisionEventual.
Section Eventual.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variable I : Type.
Variable U : I -> X -> Prop.
Let C := singular_chains Real R X.
Let inc := @small_chain_inclusion Real X I U R.
Let sd := subdivision_chain_map Real R X.

Definition small_image n := linear_image (chain_map_at inc n).

Lemma small_image_basis n (s : simplex (singular_set Real X) n)
    (hs : member (small_subcomplex Real U) n s) : small_image n (free_basis R s).
Proof.
exists (free_basis R (exist _ s hs)).
exact: free_map_basis.
Qed.

Lemma small_image_invariant n x : small_image n x -> small_image n (chain_map_at sd n x).
Proof.
move=> [y <-]; exists (@small_subdivision_at Real R X I U n y).
exact: small_subdivision_inclusion.
Qed.

Lemma subdivision_power_at k n x :
  chain_map_at (chain_power sd k) n x = linear_iter (chain_map_at sd n) k x.
Proof. by elim: k => [|k ih] //; rewrite chain_power_succ /= ih. Qed.

Lemma iterated_basis_in_subspace n k (s : simplex (singular_set Real X) n)
    (N : module_subspace (chain_term C n)) :
  (forall ps : seq {perm 'I_n.+1}, size ps = k ->
    N (free_basis R (iterated_singular_barycentric_cell ps s))) ->
  N (linear_iter (chain_map_at sd n) k (free_basis R s)).
Proof.
elim: k N => [|k ih] N hN.
- have h := hN [::] (erefl _); by rewrite iterated_singular_barycentric_cell_nil in h.
- change (N (chain_map_at sd n (linear_iter (chain_map_at sd n) k (free_basis R s)))).
  apply: (ih (linear_preimage (chain_map_at sd n) N)).
  move=> ps hps.
  change (N (subdivision_at Real R X n (free_basis R (iterated_singular_barycentric_cell ps s)))).
  rewrite subdivision_at_basis.
  apply: big_ind => [|a b ha hb|p _].
  + exact: subspace_zero.
  + exact: subspace_add ha hb.
  + apply: subspace_scale.
    rewrite -iterated_singular_barycentric_cell_cons.
    apply: hN; by rewrite /= hps.
Qed.

Variable hopen : forall i, open (U i).
Variable hcover : forall x, exists i, U i x.

Lemma basis_eventually_small n (s : simplex (singular_set Real X) n) :
  exists k, small_image n (linear_iter (chain_map_at sd n) k (free_basis R s)).
Proof.
have [k hk] := @singular_generator_eventually_small_of_cover Real X n I U hopen hcover s.
exists k; apply: iterated_basis_in_subspace => ps hps.
apply: small_image_basis; apply: hk; by rewrite hps.
Qed.

Theorem chain_eventually_small n (x : chain_term C n) :
  exists k, exists y, chain_map_at inc n y = chain_map_at (chain_power sd k) n x.
Proof.
have [k hk] := @eventual_free_chain R (simplex (singular_set Real X) n)
  (chain_map_at sd n) (small_image n) (@small_image_invariant n) (@basis_eventually_small n) x.
exists k; rewrite subdivision_power_at; exact: hk.
Qed.
End Eventual.
End DPSingularSubdivisionEventual.
