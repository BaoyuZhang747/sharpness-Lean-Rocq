(** Actual homology-bijective chain maps and representative lifting/reflection. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps.
Local Open Scope ring_scope.

Module DPChainQuasiIsomorphism.
Section QuasiIso.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.

Definition quasi_isomorphism : Prop :=
  forall n, injective (homology_map f n) /\
    (forall y, exists x, homology_map f n x = y).

Lemma quasi_iso_boundary_reflect (hf : quasi_isomorphism) n
    (x : chain_term C n) (hx : @cycle R C n x) :
    @boundary R D n (chain_map_at f n x) -> @boundary R C n x.
Proof.
move=> hb; apply/(homology_class_zero hx).
apply (proj1 (hf n)); rewrite linear0 homology_map_class.
apply/homology_class_zero; exact hb.
Qed.

Lemma quasi_iso_cycle_lift (hf : quasi_isomorphism) n
    (y : chain_term D n) (hy : @cycle R D n y) :
    exists (x : chain_term C n), exists (hx : @cycle R C n x),
      exists w : chain_term D n.+1, chain_d D n w + chain_map_at f n x = y.
Proof.
have [q hq] := proj2 (hf n) (homology_class hy).
have [z hz] := quotient_pi_surjective q.
rewrite -hz homology_map_pi /homology_class in hq.
have [w hw] := proj1 (@homology_pi_eq R D n (cycle_map f n z) (cycle_of_cycle hy)) hq.
exists (val z), (proj1 (@cycle_subspaceE R C n _) (submodule_val_mem z)), (-w).
change (chain_d D n (-w) + chain_map_at f n (val z) = y).
change (chain_d D n w = chain_map_at f n (val z) - y) in hw.
by rewrite linearN hw opprB subrK.
Qed.
End QuasiIso.
End DPChainQuasiIsomorphism.
