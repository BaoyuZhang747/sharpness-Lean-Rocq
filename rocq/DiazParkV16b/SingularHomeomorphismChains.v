(** Actual inverse singular chain maps of an actual homeomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory SingularSet SingularCohomology
  SimplicialChains SimplicialChainsMaps SingularChainMapsLaws ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPTopological DPSingularSet DPSingularCohomology
  DPSimplicialChains DPSimplicialChainMaps DPSingularChainMapsLaws DPChainComplex.
Local Open Scope ring_scope.

Module DPSingularHomeomorphismChains.
Section Homeomorphism.
Variable Real : realType.
Variable R : pzRingType.
Variables X Y : topologicalType.
Variable e : homeomorphism X Y.
Let F := singular_chain_map Real R (iso_hom e).
Let G := singular_chain_map Real R (iso_inv e).

Lemma singular_homeomorphism_forwardK n (x : chain_term (singular_chains Real R X) n) :
  chain_map_at G n (chain_map_at F n x) = x.
Proof.
rewrite /G /F -singular_chain_composition iso_hom_inv.
exact: singular_chain_identity.
Qed.

Lemma singular_homeomorphism_inverseK n (y : chain_term (singular_chains Real R Y) n) :
  chain_map_at F n (chain_map_at G n y) = y.
Proof.
rewrite /G /F -singular_chain_composition iso_inv_hom.
exact: singular_chain_identity.
Qed.

Theorem homeomorphism_positive_exact n
  (hexact : forall y, @cycle R (singular_chains Real R Y) n.+1 y ->
    @boundary R (singular_chains Real R Y) n.+1 y)
  (x : chain_term (singular_chains Real R X) n.+1) :
  @cycle R (singular_chains Real R X) n.+1 x ->
  @boundary R (singular_chains Real R X) n.+1 x.
Proof.
move=> hx.
have [y hy] := hexact _ (@chain_map_cycle R _ _ F n.+1 x hx).
exists (chain_map_at G n.+2 y).
rewrite chain_map_commutes hy; exact: singular_homeomorphism_forwardK.
Qed.

Theorem homeomorphism_augmentation_exact
  (hexact : forall y, augmentation R (singular_set Real Y) y = 0 ->
    @boundary R (singular_chains Real R Y) 0%N y)
  (x : chain_term (singular_chains Real R X) 0%N) :
  augmentation R (singular_set Real X) x = 0 ->
  @boundary R (singular_chains Real R X) 0%N x.
Proof.
move=> hx.
have he : augmentation R (singular_set Real Y) (chain_map_at F 0%N x) = 0.
  change (augmentation R (singular_set Real Y)
    (map_at R (singular_map Real (iso_hom e)) 0%N x) = 0).
  by rewrite map_augmentation.
have [y hy] := hexact _ he.
exists (chain_map_at G 1%N y).
rewrite chain_map_commutes hy; exact: singular_homeomorphism_forwardK.
Qed.

End Homeomorphism.
End DPSingularHomeomorphismChains.
