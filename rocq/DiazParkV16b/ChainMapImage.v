(** Image subcomplex and literal relative quotient of an actual chain map. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleMaps MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainSubcomplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainSubcomplex.
Local Open Scope ring_scope.

Module DPChainMapImage.
Section Images.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.

Definition image_subcomplex : chain_subcomplex D.
Proof.
refine (@ChainSubcomplex R D (fun n => linear_image (chain_map_at f n)) _).
move=> n x [y <-]; exists (chain_d C n y); symmetry; exact: chain_map_commutes.
Defined.

Definition image_factor : chain_map C (subcomplex_chain image_subcomplex).
Proof.
refine (@ChainMap R C (subcomplex_chain image_subcomplex)
  (fun n => linear_to_image (chain_map_at f n)) _).
move=> n x; apply submodule_val_injective.
change (chain_d D n (chain_map_at f n.+1 x) = chain_map_at f n (chain_d C n x)).
exact: chain_map_commutes.
Defined.

Lemma image_factor_surjective n : forall y, exists x,
  chain_map_at image_factor n x = y.
Proof. exact: linear_to_image_surjective. Qed.

Lemma image_factor_injective (h : forall n, injective (chain_map_at f n)) n :
  injective (chain_map_at image_factor n).
Proof.
move=> x y e; apply: (@h n x y).
exact: (congr1 (fun z => (val z : chain_term D n)) e).
Qed.

Lemma image_factor_equation n x :
  chain_map_at (subcomplex_inclusion image_subcomplex) n
    (chain_map_at image_factor n x) = chain_map_at f n x.
Proof. reflexivity. Qed.

Definition relative_chain := quotient_chain image_subcomplex.
Definition relative_projection := quotient_projection image_subcomplex.

Theorem relative_sequence_exact n :
  linear_exact (chain_map_at f n) (chain_map_at relative_projection n).
Proof. move=> x; exact: quotient_pi_kernel. Qed.

Theorem relative_projection_surjective n : forall q, exists x,
  chain_map_at relative_projection n x = q.
Proof. exact: quotient_projection_surjective. Qed.

Lemma relative_projection_annihilates n x :
  chain_map_at relative_projection n (chain_map_at f n x) = 0.
Proof. apply/quotient_pi_kernel; by exists x. Qed.
End Images.
End DPChainMapImage.
