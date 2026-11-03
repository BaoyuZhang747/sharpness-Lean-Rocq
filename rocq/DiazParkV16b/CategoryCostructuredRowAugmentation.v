(** Actual row-augmentation equivalence using the constructed under-category contractions. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryComma CategoryStructured BarFreeModule.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve BisimplicialSet BisimplicialChains
 ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialChains SimplicialChainsMaps SimplicialSigma SimplicialReplacementConstants
 SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementAugmentation CategoryCostructuredDiagram CategoryCostructuredNerveEndpoint
 CategoryCostructuredReplacementRows CategoryCostructuredReplacementRowMaps CategoryNerveSigmaContraction CategoryUnderContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPBisimplicialSet DPBisimplicialChains
 DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialChains DPSimplicialChainMaps DPSimplicialSigma DPSimplicialReplacementConstants
 DPSimplicialReplacementTypes DPSimplicialReplacement DPSimplicialReplacementAugmentation DPCategoryCostructuredDiagram DPCategoryCostructuredReplacementRows DPCategoryCostructuredReplacementRowMaps DPCategoryNerveSigmaContraction DPCategoryUnderContraction.
Local Open Scope ring_scope.
Module DPCategoryCostructuredRowAugmentation.
Section Augmentation.
Variables C D : category.
Variable T : functor C D.
Local Notation F := (costructured_nerve_diagram T).
Definition projection_cocone : nat_trans F (@constant_diagram D simplicial_category (nerve C)).
Proof.
refine (@Build_nat_trans D simplicial_category F (@constant_diagram D simplicial_category (nerve C)) (costructured_projection_nerve T) _).
move=>d e f; apply nat_trans_ext=>n; apply type_morphism_ext=>s.
exact: projection_nerve_natural.
Defined.
Definition costructured_augmentation : bisimplicial_map (replacement F) (horizontal_constant (nerve C)) := coefficient_augmentation projection_cocone.
Definition row_projection q : simplicial_map (row_model_set T q) (constant_simplicial (simplex (nerve C) q)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (row_model_set T q) (constant_simplicial (simplex (nerve C) q)) (fun p x=>projT1 x) _).
move=>p m f; apply type_morphism_ext=>[[c u]]; reflexivity.
Defined.
Variable R : pzRingType.
Lemma row_projection_quasi_isomorphism q : quasi_isomorphism (chain_map_of R (row_projection q)).
Proof.
change (quasi_isomorphism (chain_map_of R (sigma_projection (fun c : simplex (nerve C) q=>nerve (structured_category (functor_id D) (row_anchor T c)))))).
exact (@nerve_sigma_projection_quasi_isomorphism (simplex (nerve C) q)
 (fun c=>structured_category (functor_id D) (row_anchor T c))
 (fun c=>@under_initial D (row_anchor T c)) (fun c=>@under_initial_nat_trans D (row_anchor T c)) R).
Qed.
Lemma row_forward_quasi_isomorphism q : quasi_isomorphism (chain_map_of R (row_forward_map T q)).
Proof.
apply degreewise_bijective_quasi_isomorphism.
- move=>n x y hxy.
  have hi (z:term R (horizontal_simplicial (replacement F) q) n) :
    map_at R (row_backward_map T q) n (map_at R (row_forward_map T q) n z)=z.
    rewrite -map_composition.
    have he : nat_comp (row_forward_map T q) (row_backward_map T q)=nat_id (horizontal_simplicial (replacement F) q).
      exact: iso_hom_inv (row_isomorphism T q).
    rewrite he; exact: map_identity.
  by rewrite -(hi x) -(hi y) hxy.
- move=>n y; exists (map_at R (row_backward_map T q) n y).
  rewrite -map_composition.
  have he : nat_comp (row_backward_map T q) (row_forward_map T q)=nat_id (row_model_set T q).
    exact: iso_inv_hom (row_isomorphism T q).
  rewrite he; exact: map_identity.
Qed.
End Augmentation.
End DPCategoryCostructuredRowAugmentation.
