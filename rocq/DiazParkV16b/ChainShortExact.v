(** Degreewise exact sequences of actual downward chain complexes. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainSubcomplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainSubcomplex.
Local Open Scope ring_scope.
Module DPChainShortExact.
Section Exact.
Variable R : pzRingType.
Variables A B C : chain_complex R.
Variables (f : chain_map A B) (g : chain_map B C).
Record chain_short_exact := ChainShortExact {
  exact_injective : forall n, injective (chain_map_at f n);
  exact_composite : forall n x, chain_map_at g n (chain_map_at f n x) = 0;
  exact_kernel : forall n x, chain_map_at g n x = 0 -> exists y, chain_map_at f n y = x;
  exact_surjective : forall n z, exists y, chain_map_at g n y = z
}.
End Exact.

Definition subcomplex_short_exact (R : pzRingType) (C : chain_complex R)
    (S : chain_subcomplex C) :
  chain_short_exact (subcomplex_inclusion S) (quotient_projection S).
Proof.
constructor.
- exact: subcomplex_inclusion_injective.
- move=> n x; apply/quotient_projection_kernel; by exists x.
- move=> n x; exact: (proj1 (@quotient_projection_kernel R C S n x)).
- exact: quotient_projection_surjective.
Defined.
End DPChainShortExact.
