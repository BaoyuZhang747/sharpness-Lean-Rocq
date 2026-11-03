(** Native homology comparison from explicit subdivision-type algebraic data. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalModuleIso.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainIteration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainIteration DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPSmallChainComparison.
Section Comparison.
Variable R : pzRingType.
Variables S C : chain_complex R.
Variable i : chain_map S C.
Variable hi : forall n, injective (chain_map_at i n).
Variable t : chain_map S S.
Variable s : chain_map C C.
Variable w : forall n x, chain_map_at i n (chain_map_at t n x) =
  chain_map_at s n (chain_map_at i n x).
Variable ht : chain_homotopy t (chain_identity S).
Variable hs : chain_homotopy s (chain_identity C).
Variable hevent : forall n (x : chain_term C n), exists k, exists y,
  chain_map_at i n y = chain_map_at (chain_power s k) n x.
Arguments hevent n x : clear implicits.

Lemma eventual_boundary_reflection n (x : chain_term S n)
    (hx : @cycle R S n x) :
  @boundary R C n (chain_map_at i n x) -> @boundary R S n x.
Proof.
move=> [y hy]; have [k [z hz]] := hevent n.+1 y.
have hd : chain_d S n z = chain_map_at (chain_power t k) n x.
  apply: (@hi n).
  rewrite -chain_map_commutes hz chain_map_commutes hy.
  symmetry; exact: (@chain_power_commutes R S C i t s w k n x).
have hz0 : homology_map (chain_power t k) n (homology_class hx) = 0.
  rewrite homology_map_class; apply/homology_class_zero; by exists z.
rewrite (chain_power_homology ht) in hz0.
exact: (proj1 (homology_class_zero hx) hz0).
Qed.

Lemma homology_kernel_zero n (q : homology S n) :
  homology_map i n q = 0 -> q = 0.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite homology_map_pi => h; apply/quotient_pi_kernel; apply/boundary_subspaceE.
apply: (@eventual_boundary_reflection n (val z)).
- apply/cycle_subspaceE; exact: submodule_val_mem.
- have hb := (proj1 (quotient_pi_kernel _ _) h).
  exact: hb.
Qed.

Theorem homology_injective n : injective (homology_map i n).
Proof.
move=> x y h; apply/subr0_eq.
apply homology_kernel_zero; by rewrite linearB h subrr.
Qed.

Theorem homology_surjective n : forall q : homology C n, exists r,
  homology_map i n r = q.
Proof.
move=> q; have [z <-] := quotient_pi_surjective q.
have hz : @cycle R C n (val z) by apply/cycle_subspaceE; exact: submodule_val_mem.
have [k [y hy]] := hevent n (val z).
have hyc : @cycle R S n y.
  apply: (@cycle_of_injective_map R S C i hi n y).
  rewrite hy; exact: (@chain_map_cycle R C C (chain_power s k) n (val z) hz).
exists (homology_class hyc).
have e : homology_map i n (homology_class hyc) =
  homology_map (chain_power s k) n (quotient_pi (boundaries_in_cycles C n) z).
  rewrite /homology_class !homology_map_pi; apply/homology_pi_eq.
  change (@boundary R C n (chain_map_at i n y - chain_map_at (chain_power s k) n (val z))).
  rewrite hy subrr; exists 0; exact: linear0.
by rewrite e (chain_power_homology hs).
Qed.

Definition comparison_iso n : @isomorphism (module_category R)
    [the lmodType R of homology S n] [the lmodType R of homology C n] :=
  @linear_bijection_iso R _ _ (homology_map i n)
    (@homology_injective n) (@homology_surjective n).

Lemma comparison_iso_hom n (q : homology S n) :
  module_hom_fun (iso_hom (comparison_iso n)) q = homology_map i n q.
Proof. reflexivity. Qed.
End Comparison.
End DPSmallChainComparison.
