(** The coproduct comparison on actual singular chains is degreewise invertible. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainDegreewiseIso
  SimplicialSet SimplicialCopower SimplicialChains SimplicialChainsMaps SingularSet SingularCohomology
  SingularCoproductComponents FreeModuleEmbeddings FreeModuleSurjections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps DPChainDegreewiseIso
  DPSimplicialSet DPSimplicialCopower DPSimplicialChains DPSimplicialChainMaps
  DPSingularSet DPSingularCohomology DPSingularCoproductComponents
  DPFreeModuleEmbeddings DPFreeModuleSurjections.

Module DPSingularCoproductChains.
Section Copower.
Variable Real : realType.
Variable R : pzRingType.
Variable I : Type.
Variable X : topologicalType.

Definition singular_copower_chain_map : chain_map
    (chains R (copower I (singular_set Real X)))
    (singular_chains Real R (space_copower I X)) :=
  chain_map_of R (singular_copower_map Real I X).

Lemma singular_copower_chain_map_injective n : injective (chain_map_at singular_copower_chain_map n).
Proof. apply: free_map_injective; exact: singular_copower_map_injective. Qed.
Lemma singular_copower_chain_map_surjective n y :
  exists x, chain_map_at singular_copower_chain_map n x = y.
Proof. apply: free_map_surjective; exact: singular_copower_map_surjective. Qed.

Definition singular_copower_homology_iso n :=
  @degreewise_homology_iso R _ _ singular_copower_chain_map
    singular_copower_chain_map_injective singular_copower_chain_map_surjective n.

Lemma singular_copower_homology_iso_hom n q :
  module_hom_fun (iso_hom (singular_copower_homology_iso n)) q =
    homology_map singular_copower_chain_map n q.
Proof. reflexivity. Qed.
End Copower.
End DPSingularCoproductChains.
