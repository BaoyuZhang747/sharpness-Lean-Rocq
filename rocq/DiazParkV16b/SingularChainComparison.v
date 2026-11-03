(** Actual injections, homeomorphisms, and deformation retractions on singular chains. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  SingularSet SingularCohomology SingularChainMapsLaws SingularChainHomotopy SingularHomeomorphismChains
  SimplicialSet ChainComplex ChainHomology ChainHomologyMaps ChainQuasiIsomorphism
  ChainQuasiIsomorphismLaws FreeModuleEmbeddings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPSingularSet DPSingularCohomology
  DPSingularChainMapsLaws DPSingularChainHomotopy DPSingularHomeomorphismChains
  DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism
  DPChainQuasiIsomorphismLaws DPFreeModuleEmbeddings.
Module DPSingularChainComparison.
Section Comparison.
Variable Real : realType.
Variable R : pzRingType.

Theorem singular_chains_injective (X Y : topologicalType) (f : continuousType X Y)
    (hf : injective f) n : injective (chain_map_at (singular_chain_map Real R f) n).
Proof.
apply: free_map_injective => s t h.
apply/continuousEP => x; apply: hf.
exact (congr1 (fun a : DPSimplicialSet.simplex (singular_set Real Y) n => a x) h).
Qed.

Lemma singular_homology_identity (X : topologicalType) n (q : homology (singular_chains Real R X) n) :
  homology_map (singular_chain_map Real R (continuous_identity X)) n q = q.
Proof.
rewrite (@homology_map_ext R _ _ _ (chain_identity _) (@singular_chain_identity Real R X) n q).
exact: homology_map_identity.
Qed.

Lemma singular_homology_composition (X Y Z : topologicalType)
    (f : continuousType X Y) (g : continuousType Y Z) n
    (q : homology (singular_chains Real R X) n) :
  homology_map (singular_chain_map Real R (continuous_compose f g)) n q =
    homology_map (singular_chain_map Real R g) n (homology_map (singular_chain_map Real R f) n q).
Proof.
rewrite -homology_map_composition.
apply: homology_map_ext; exact: singular_chain_composition.
Qed.

Theorem singular_homeomorphism_quasi_isomorphism (X Y : topologicalType) (e : homeomorphism X Y) :
  quasi_isomorphism (singular_chain_map Real R (iso_hom e)).
Proof.
apply: degreewise_bijective_quasi_isomorphism.
- move=> n; exact: (can_inj (@singular_homeomorphism_forwardK Real R X Y e n)).
- move=> n y; exists (chain_map_at (singular_chain_map Real R (iso_inv e)) n y).
  exact: singular_homeomorphism_inverseK.
Qed.

Variables X Y : topologicalType.
Variables (s : continuousType X Y) (r : continuousType Y X).
Variable hsr : forall x, r (s x) = x.
Variable H : continuous_homotopy Real (continuous_identity Y) (continuous_compose r s).

Lemma retraction_homology_left n (q : homology (singular_chains Real R X) n) :
  homology_map (singular_chain_map Real R r) n (homology_map (singular_chain_map Real R s) n q) = q.
Proof.
rewrite -singular_homology_composition.
have e : continuous_compose s r = continuous_identity X.
  apply/continuousEP; exact hsr.
rewrite e; exact: singular_homology_identity.
Qed.

Lemma retraction_homology_right n (q : homology (singular_chains Real R Y) n) :
  homology_map (singular_chain_map Real R s) n (homology_map (singular_chain_map Real R r) n q) = q.
Proof.
rewrite -singular_homology_composition (singular_homology_homotopy H q).
exact: singular_homology_identity.
Qed.

Theorem deformation_retraction_quasi_isomorphism : quasi_isomorphism (singular_chain_map Real R s).
Proof.
move=> n; split.
- exact: (can_inj (@retraction_homology_left n)).
- move=> y; exists (homology_map (singular_chain_map Real R r) n y).
  exact: retraction_homology_right.
Qed.
End Comparison.
End DPSingularChainComparison.
