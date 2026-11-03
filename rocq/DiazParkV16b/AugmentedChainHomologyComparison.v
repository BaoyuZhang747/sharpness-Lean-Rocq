(** A literal chain map between augmented exact complexes induces an isomorphism.
    All hypotheses concern the given complexes and maps, including degree zero. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalModuleIso.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPAugmentedChainHomologyComparison.
Section Comparison.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Variables (eC : {linear chain_term C 0%N -> R^o})
  (eD : {linear chain_term D 0%N -> R^o}).
Hypothesis eD_boundary : forall x, eD (chain_d D 0%N x) = 0.
Hypothesis augmentation_commutes : forall x, eD (chain_map_at f 0%N x) = eC x.
Hypothesis eC_surjective : forall r, exists x, eC x = r.
Hypothesis C_zero_exact : forall x, eC x = 0 -> @boundary R C 0%N x.
Hypothesis D_zero_exact : forall x, eD x = 0 -> @boundary R D 0%N x.
Hypothesis C_positive_exact : forall n x, @cycle R C n.+1 x -> @boundary R C n.+1 x.
Hypothesis D_positive_exact : forall n x, @cycle R D n.+1 x -> @boundary R D n.+1 x.

Lemma comparison_kernel_zero n (q : homology C n) :
  homology_map f n q = 0 -> q = 0.
Proof.
case: n q => [|n] q.
- have [z <-] := quotient_pi_surjective q.
  rewrite homology_map_pi => hq.
  have hb := proj1 (quotient_pi_kernel _ _) hq.
  change (@boundary R D 0%N (chain_map_at f 0%N (val z))) in hb.
  have [b eb] := hb.
  apply/quotient_pi_kernel.
  change (@boundary R C 0%N (val z)).
  apply: C_zero_exact.
  rewrite -augmentation_commutes -eb; exact: eD_boundary.
- move=> _. exact: (proj2 (@homology_zero_iff R C n.+1) (@C_positive_exact n) q).
Qed.

Theorem comparison_injective n : injective (homology_map f n).
Proof.
move=> x y h; apply/subr0_eq.
apply: comparison_kernel_zero. by rewrite linearB h subrr.
Qed.

Theorem comparison_surjective n : forall q : homology D n,
  exists r, homology_map f n r = q.
Proof.
case: n => [|n] q.
- have [z <-] := quotient_pi_surjective q.
  have [x hx] := eC_surjective (eD (val z)).
  exists (@homology_class R C 0%N x I).
  rewrite /homology_class homology_map_pi.
  apply/homology_pi_eq.
  change (@boundary R D 0%N (chain_map_at f 0%N x - val z)).
  apply: D_zero_exact. by rewrite linearB augmentation_commutes hx subrr.
- exists 0; rewrite linear0.
  symmetry; exact: (proj2 (@homology_zero_iff R D n.+1) (@D_positive_exact n) q).
Qed.

Definition augmented_comparison_iso n : @isomorphism (module_category R)
    [the lmodType R of homology C n] [the lmodType R of homology D n] :=
  @linear_bijection_iso R _ _ (homology_map f n)
    (@comparison_injective n) (@comparison_surjective n).

Lemma augmented_comparison_iso_hom n (q : homology C n) :
  module_hom_fun (iso_hom (augmented_comparison_iso n)) q = homology_map f n q.
Proof. reflexivity. Qed.

End Comparison.
End DPAugmentedChainHomologyComparison.
