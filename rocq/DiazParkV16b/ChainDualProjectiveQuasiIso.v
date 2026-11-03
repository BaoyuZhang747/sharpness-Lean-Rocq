(** Arbitrary coefficient modules preserve the actual projective-chain comparison
    under Hom(-,A), through the constructed homotopy inverse. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  HomologicalMaps HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainDualCochain CochainMapsLaws
  LinearProjective ChainQuasiIsomorphism ChainProjectiveQuasiIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainDualCochain DPCochainMapsLaws
  DPLinearProjective DPChainQuasiIsomorphism DPChainProjectiveQuasiIso
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.

Module DPChainDualProjectiveQuasiIso.
Section Duality.
Variable R : comPzRingType.
Variable A : lmodType R.

Lemma dual_cohomology_identity (C : chain_complex R) n (x : cohomology (dual_complex A C) n) :
  cohomology_map (dual_map A (chain_identity C)) n x = x.
Proof. apply cohomology_identity_of; exact: dual_identity_at. Qed.

Lemma dual_cohomology_composition (C D E : chain_complex R)
    (f : chain_map C D) (g : chain_map D E) n (x : cohomology (dual_complex A E) n) :
  cohomology_map (dual_map A (chain_composition f g)) n x =
    cohomology_map (dual_map A f) n (cohomology_map (dual_map A g) n x).
Proof. apply cohomology_composition_of; exact: dual_composition_at. Qed.

Variables C D : chain_complex R.
Variable f : chain_map C D.
Variable hC : forall n, linear_projective (chain_term C n).
Variable hD : forall n, linear_projective (chain_term D n).
Variable hf : quasi_isomorphism f.
Let g := @quasi_iso_inverse R C D f hC hD hf.

Definition dual_projective_cohomology_iso n : @isomorphism (module_category R)
  [the lmodType R of cohomology (dual_complex A D) n]
  [the lmodType R of cohomology (dual_complex A C) n].
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (cohomology_map (dual_map A f) n))
  (module_hom_of_linear (cohomology_map (dual_map A g) n)) _ _).
- apply module_hom_ext => q.
  change (cohomology_map (dual_map A g) n (cohomology_map (dual_map A f) n q) = q).
  rewrite -dual_cohomology_composition.
  have hh := @quasi_iso_target_homotopy R C D f hC hD hf.
  rewrite (cohomology_map_homotopy (dual_homotopy A hh)).
  exact: dual_cohomology_identity.
- apply module_hom_ext => q.
  change (cohomology_map (dual_map A f) n (cohomology_map (dual_map A g) n q) = q).
  rewrite -dual_cohomology_composition.
  have hh := @quasi_iso_source_homotopy R C D f hC hD hf.
  rewrite (cohomology_map_homotopy (dual_homotopy A hh)).
  exact: dual_cohomology_identity.
Defined.

Lemma dual_projective_cohomology_iso_hom n x :
  module_hom_fun (iso_hom (dual_projective_cohomology_iso n)) x =
  cohomology_map (dual_map A f) n x.
Proof. reflexivity. Qed.
End Duality.
End DPChainDualProjectiveQuasiIso.
