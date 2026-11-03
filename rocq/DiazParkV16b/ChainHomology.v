(** Actual cycles modulo boundaries for plain downward chain complexes. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex.
Local Open Scope ring_scope.

Module DPChainHomology.
Section Homology.
Variable R : pzRingType.

Definition cycle_subspace (C : @chain_complex R) n : module_subspace (chain_term C n) :=
  match n as k return module_subspace (chain_term C k) with
  | 0%N => subspace_full (chain_term C 0%N)
  | k.+1 => linear_kernel (chain_d C k)
  end.

Lemma cycle_subspaceE (C : @chain_complex R) n (x : chain_term C n) :
  cycle_subspace C n x <-> @cycle R C n x.
Proof. by case: n x. Qed.

Definition boundary_subspace (C : @chain_complex R) n := linear_image (chain_d C n).

Lemma boundary_subspaceE (C : @chain_complex R) n (x : chain_term C n) :
  boundary_subspace C n x <-> @boundary R C n x.
Proof. reflexivity. Qed.

Lemma boundaries_are_cycles (C : @chain_complex R) n :
  subspace_le (boundary_subspace C n) (cycle_subspace C n).
Proof.
move=> x /boundary_subspaceE hx; apply/cycle_subspaceE.
exact: boundary_cycle hx.
Qed.

Definition cycle_module (C : @chain_complex R) n := submodule_carrier (cycle_subspace C n).

Definition cycle_inclusion (C : @chain_complex R) n :
    {linear cycle_module C n -> chain_term C n} :=
  (val : {linear cycle_module C n -> chain_term C n}).

Definition boundaries_in_cycles (C : @chain_complex R) n :=
  linear_preimage (cycle_inclusion C n) (boundary_subspace C n).

Definition homology (C : @chain_complex R) n := module_quotient (boundaries_in_cycles C n).

Definition cycle_of_cycle (C : @chain_complex R) n (x : chain_term C n)
    (hx : @cycle R C n x) : cycle_module C n :=
  @submodule_in R (chain_term C n) (cycle_subspace C n) x
    (proj2 (@cycle_subspaceE C n x) hx).

Definition homology_class (C : @chain_complex R) n (x : chain_term C n)
    (hx : @cycle R C n x) : homology C n :=
  quotient_pi (boundaries_in_cycles C n) (cycle_of_cycle hx).

Lemma homology_class_zero (C : @chain_complex R) n (x : chain_term C n)
    (hx : @cycle R C n x) : homology_class hx = 0 <-> @boundary R C n x.
Proof.
rewrite /homology_class quotient_pi_kernel.
exact: boundary_subspaceE.
Qed.

Theorem homology_zero_iff (C : @chain_complex R) n :
    (forall q : homology C n, q = 0) <->
    (forall x : chain_term C n, @cycle R C n x -> @boundary R C n x).
Proof.
split.
- move=> h x hx; apply/(homology_class_zero hx); exact: h.
- move=> h q; have [z <-] := quotient_pi_surjective q.
  apply/quotient_pi_kernel; apply/boundary_subspaceE; apply: h.
  apply/cycle_subspaceE; exact: submodule_val_mem.
Qed.

Theorem acyclic_homology (C : @chain_complex R) :
  acyclic C <-> forall n (q : homology C n), q = 0.
Proof.
split.
- move=> h n; apply/homology_zero_iff; exact: h n.
- move=> h n; apply/homology_zero_iff; exact: h n.
Qed.

End Homology.
End DPChainHomology.
