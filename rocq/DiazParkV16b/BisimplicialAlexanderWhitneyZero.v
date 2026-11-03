(** The literal degree-zero Alexander--Whitney isomorphism. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalModuleIso BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplexCategory SimplicialSet
  BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyOrdinals
  BisimplicialAlexanderWhitneyFaces BisimplicialAlexanderWhitneyChain FirstQuadrantChainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DiazParkFreeModule DPChainComplex DPSimplexCategory
  DPSimplicialSet DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyOrdinals
  DPAlexanderWhitneyFaces DPAlexanderWhitneyChain DPFirstQuadrantChainTotal.
Local Open Scope ring_scope.

Module DPAlexanderWhitneyZero.
Lemma aw_simplex_zero (X : bisimplicial_set) (x : simplex (diagonal X) 0%N) :
  aw_simplex X 0%N 0%N 0%N erefl x = x.
Proof.
have hf : front 0%N 0%N 0%N erefl = ordinal_map_identity 0%N.
  apply ordinal_map_ext => i; apply val_inj; reflexivity.
have hb : back 0%N 0%N 0%N erefl = ordinal_map_identity 0%N.
  apply ordinal_map_ext => i; apply val_inj; reflexivity.
by rewrite /aw_simplex hf hb bisimplex_map_identity.
Qed.

Section Zero.
Variable R : pzRingType.
Variable X : bisimplicial_set.
Let C := diagonal_chains R X.
Let T := total_chains R X.
Let aw := alexander_whitney R X.
Definition aw_zero_inverse (a : chain_term T 0%N) : chain_term C 0%N := a 0%N 0%N erefl.
Lemma aw_zero_inverse_linear : linear aw_zero_inverse.
Proof. by move=> r a b. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _ aw_zero_inverse aw_zero_inverse_linear.

Lemma aw_zero_left (a : chain_term C 0%N) : aw_zero_inverse (chain_map_at aw 0%N a) = a.
Proof.
change (free_map R (aw_simplex X 0%N 0%N 0%N erefl) a = a).
have e : aw_simplex X 0%N 0%N 0%N erefl = idfun.
  apply functional_extensionality_dep => x; exact: aw_simplex_zero.
rewrite e; exact: free_map_identity.
Qed.

Lemma aw_zero_right (a : chain_term T 0%N) : chain_map_at aw 0%N (aw_zero_inverse a) = a.
Proof.
apply functional_extensionality_dep => p; apply functional_extensionality_dep => q;
  apply functional_extensionality_dep => h.
case: p h => [|p] h; last discriminate.
case: q h => [|q] h; last discriminate.
have eh : h = erefl by apply Prop_irrelevance.
rewrite eh.
change (aw_zero_inverse (chain_map_at aw 0%N (aw_zero_inverse a)) = aw_zero_inverse a).
exact: aw_zero_left.
Qed.

Lemma aw_zero_injective : injective (chain_map_at aw 0%N).
Proof. move=> a b h; by rewrite -[a]aw_zero_left -[b]aw_zero_left h. Qed.
Lemma aw_zero_surjective b : exists a, chain_map_at aw 0%N a = b.
Proof. exists (aw_zero_inverse b); exact: aw_zero_right. Qed.

Definition alexander_whitney_zero_iso : @isomorphism (module_category R) (chain_term C 0%N) (chain_term T 0%N) :=
  linear_bijection_iso aw_zero_injective aw_zero_surjective.
Lemma alexander_whitney_zero_iso_hom a : module_hom_fun (iso_hom alexander_whitney_zero_iso) a =
  chain_map_at aw 0%N a.
Proof. reflexivity. Qed.
End Zero.
End DPAlexanderWhitneyZero.
