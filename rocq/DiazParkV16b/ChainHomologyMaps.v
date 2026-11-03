(** Actual induced maps and homotopy invariance on downward-chain homology. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps.
From DiazParkV16b Require Import ChainComplex ChainHomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology.
Local Open Scope ring_scope.

Module DPChainHomologyMaps.

Section Maps.
Variable R : pzRingType.
Variables C D : @chain_complex R.
Variable f : chain_map C D.

Definition cycle_map n : {linear cycle_module C n -> cycle_module D n} :=
  @submodule_map R (chain_term C n) (chain_term D n)
    (chain_map_at f n) (cycle_subspace C n) (cycle_subspace D n)
    (fun x hx => proj2 (@cycle_subspaceE R D n _)
      (@chain_map_cycle R C D f n x (proj1 (@cycle_subspaceE R C n x) hx))).

Lemma cycle_map_val n (z : cycle_module C n) :
  cycle_inclusion D n (cycle_map n z) = chain_map_at f n (cycle_inclusion C n z).
Proof. reflexivity. Qed.

Lemma cycle_map_boundary n (z : cycle_module C n) :
  boundaries_in_cycles C n z -> boundaries_in_cycles D n (cycle_map n z).
Proof.
move=> hz.
change (boundary_subspace D n (chain_map_at f n (cycle_inclusion C n z))).
apply/boundary_subspaceE; apply: chain_map_boundary.
by apply/boundary_subspaceE.
Qed.

Definition homology_map n : {linear homology C n -> homology D n} :=
  @quotient_map R (cycle_module C n) (cycle_module D n) (cycle_map n)
    (boundaries_in_cycles C n) (boundaries_in_cycles D n)
    (@cycle_map_boundary n).

Lemma homology_map_pi n (z : cycle_module C n) :
  homology_map n (quotient_pi (boundaries_in_cycles C n) z) =
    quotient_pi (boundaries_in_cycles D n) (cycle_map n z).
Proof. exact: quotient_map_pi. Qed.

Lemma homology_map_class n (x : chain_term C n) (hx : @cycle R C n x) :
  homology_map n (homology_class hx) =
    homology_class (@chain_map_cycle R C D f n x hx).
Proof.
rewrite /homology_class homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective; reflexivity.
Qed.

End Maps.

Section Laws.
Variable R : pzRingType.

Lemma homology_pi_eq (C : @chain_complex R) n (x y : cycle_module C n) :
  quotient_pi (boundaries_in_cycles C n) x =
      quotient_pi (boundaries_in_cycles C n) y <->
    @boundary R C n (cycle_inclusion C n x - cycle_inclusion C n y).
Proof.
split.
- move=> h; apply/boundary_subspaceE.
  have hm : boundaries_in_cycles C n (x - y).
    apply/subspace_predP; rewrite -quotient_pi_eq.
    by apply/eqP.
  change (boundary_subspace C n (cycle_inclusion C n (x - y))) in hm.
  by rewrite linearB in hm.
- move=> h; apply/eqP; rewrite quotient_pi_eq; apply/subspace_predP.
  change (boundary_subspace C n (cycle_inclusion C n (x - y))).
  rewrite linearB; by apply/boundary_subspaceE.
Qed.

Lemma homology_map_identity (C : @chain_complex R) n
    (q : homology C n) : homology_map (chain_identity C) n q = q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite homology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Lemma homology_map_composition (C D E : @chain_complex R)
    (f : chain_map C D) (g : chain_map D E) n (q : homology C n) :
  homology_map (chain_composition f g) n q =
    homology_map g n (homology_map f n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !homology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Theorem homology_map_homotopy (C D : @chain_complex R)
    (f g : chain_map C D) (h : chain_homotopy f g)
    n (q : homology C n) : homology_map f n q = homology_map g n q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !homology_map_pi; apply/homology_pi_eq.
change (@boundary R D n
  (chain_map_at f n (cycle_inclusion C n z) -
    chain_map_at g n (cycle_inclusion C n z))).
exact: (@chain_homotopy_boundary R C D f g h n
  (cycle_inclusion C n z)
    (proj1 (@cycle_subspaceE R C n _) (submodule_val_mem z))).
Qed.

End Laws.
End DPChainHomologyMaps.
