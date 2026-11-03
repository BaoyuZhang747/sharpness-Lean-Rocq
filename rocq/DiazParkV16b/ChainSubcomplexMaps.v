(** Actual maps on subcomplexes and relative chain quotients. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleMaps MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainSubcomplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainSubcomplex.
Local Open Scope ring_scope.

Module DPChainSubcomplexMaps.
Section Maps.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Variable S : chain_subcomplex C.
Variable T : chain_subcomplex D.
Variable hf : forall n x, subspace_at S n x -> subspace_at T n (chain_map_at f n x).
Arguments hf n x _ : clear implicits.

Definition subcomplex_map : chain_map (subcomplex_chain S) (subcomplex_chain T).
Proof.
refine (@ChainMap R (subcomplex_chain S) (subcomplex_chain T)
  (fun n => @submodule_map R _ _ (chain_map_at f n)
    (subspace_at S n) (subspace_at T n) (hf n)) _).
move=> n x; apply submodule_val_injective.
change (chain_d D n (chain_map_at f n.+1 (val x)) =
  chain_map_at f n (chain_d C n (val x))).
exact: chain_map_commutes.
Defined.

Lemma subcomplex_map_inclusion n x :
  chain_map_at (subcomplex_inclusion T) n (chain_map_at subcomplex_map n x) =
  chain_map_at f n (chain_map_at (subcomplex_inclusion S) n x).
Proof. reflexivity. Qed.

Definition relative_map : chain_map (quotient_chain S) (quotient_chain T).
Proof.
refine (@ChainMap R (quotient_chain S) (quotient_chain T)
  (fun n => @quotient_map R _ _ (chain_map_at f n)
    (subspace_at S n) (subspace_at T n) (hf n)) _).
move=> n q; have [x <-] := quotient_pi_surjective q.
change (quotient_d T n (quotient_map (hf n.+1) (quotient_pi (subspace_at S n.+1) x)) =
  quotient_map (hf n) (quotient_d S n (quotient_pi (subspace_at S n.+1) x))).
by rewrite quotient_map_pi !quotient_d_pi quotient_map_pi chain_map_commutes.
Defined.

Lemma relative_map_projection n x :
  chain_map_at relative_map n (chain_map_at (quotient_projection S) n x) =
  chain_map_at (quotient_projection T) n (chain_map_at f n x).
Proof. exact: quotient_map_pi. Qed.
End Maps.
End DPChainSubcomplexMaps.
