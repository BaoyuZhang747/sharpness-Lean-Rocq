(** Actual subcomplexes and quotient chain complexes of arbitrary modules. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleMaps MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex.
Local Open Scope ring_scope.

Module DPChainSubcomplex.
Section Subcomplexes.
Variable R : pzRingType.
Variable C : chain_complex R.

Record chain_subcomplex := ChainSubcomplex {
  subspace_at : forall n, module_subspace (chain_term C n);
  subspace_d : forall n x, subspace_at n.+1 x -> subspace_at n (chain_d C n x)
}.

Definition subcomplex_term (S : chain_subcomplex) n : lmodType R :=
  [the lmodType R of submodule_carrier (subspace_at S n)].
Definition subcomplex_d (S : chain_subcomplex) n :
    {linear subcomplex_term S n.+1 -> subcomplex_term S n} :=
  @submodule_map R (chain_term C n.+1) (chain_term C n) (chain_d C n)
    (subspace_at S n.+1) (subspace_at S n) (@subspace_d S n).

Definition subcomplex_chain (S : chain_subcomplex) : chain_complex R.
Proof.
refine (@ChainComplex R (subcomplex_term S) (subcomplex_d S) _).
move=> n x; apply submodule_val_injective.
change (chain_d C n (chain_d C n.+1 (val x)) = 0); exact: chain_d2.
Defined.

Definition subcomplex_inclusion (S : chain_subcomplex) : chain_map (subcomplex_chain S) C.
Proof.
refine (@ChainMap R (subcomplex_chain S) C
  (fun n => (val : {linear subcomplex_term S n -> chain_term C n})) _).
by move=> n x.
Defined.

Lemma subcomplex_inclusion_injective (S : chain_subcomplex) n :
  injective (chain_map_at (subcomplex_inclusion S) n).
Proof. exact: submodule_val_injective. Qed.

Definition quotient_term (S : chain_subcomplex) n : lmodType R :=
  [the lmodType R of module_quotient (subspace_at S n)].
Definition quotient_d (S : chain_subcomplex) n :
    {linear quotient_term S n.+1 -> quotient_term S n} :=
  @quotient_map R (chain_term C n.+1) (chain_term C n) (chain_d C n)
    (subspace_at S n.+1) (subspace_at S n) (@subspace_d S n).

Lemma quotient_d_pi (S : chain_subcomplex) n x :
  quotient_d S n (quotient_pi (subspace_at S n.+1) x) =
  quotient_pi (subspace_at S n) (chain_d C n x).
Proof. exact: quotient_map_pi. Qed.

Definition quotient_chain (S : chain_subcomplex) : chain_complex R.
Proof.
refine (@ChainComplex R (quotient_term S) (quotient_d S) _).
move=> n q; have [x <-] := quotient_pi_surjective q.
by rewrite /quotient_d !quotient_map_pi chain_d2 linear0.
Defined.

Definition quotient_projection (S : chain_subcomplex) : chain_map C (quotient_chain S).
Proof.
refine (@ChainMap R C (quotient_chain S)
  (fun n => (quotient_pi (subspace_at S n) : {linear _ -> _})) _).
move=> n x; exact: quotient_map_pi.
Defined.

Lemma quotient_projection_surjective (S : chain_subcomplex) n :
  forall q, exists x, chain_map_at (quotient_projection S) n x = q.
Proof. exact: quotient_pi_surjective. Qed.

Lemma quotient_projection_kernel (S : chain_subcomplex) n (x : chain_term C n) :
  chain_map_at (quotient_projection S) n x = 0 <->
    exists y, chain_map_at (subcomplex_inclusion S) n y = x.
Proof.
change (quotient_pi (subspace_at S n) x = 0 <->
  exists y : subcomplex_term S n, val y = x).
rewrite quotient_pi_kernel; split.
- move=> hx; exists (@submodule_in R (chain_term C n) (subspace_at S n) x hx); reflexivity.
- move=> [y <-]; exact: submodule_val_mem.
Qed.
End Subcomplexes.
End DPChainSubcomplex.
