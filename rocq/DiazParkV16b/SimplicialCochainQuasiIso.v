(** Homology isomorphisms of actual free simplicial chains induce the literal cohomology pullback isomorphism for every coefficient module. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness CategoryComplexIso
 HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
 BarFreeModule MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainDualCochain LinearMapSpace FreeLinearMapSpace LinearProjective ChainQuasiIsomorphism ChainDualProjectiveQuasiIso
 SimplicialSet SimplicialChains SimplicialChainsMaps SimplicialCochains SimplicialCochainMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
 DPChainComplex DPChainDualCochain DPLinearMapSpace DPFreeLinearMapSpace DPLinearProjective DPChainQuasiIsomorphism DPChainDualProjectiveQuasiIso
 DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPSimplicialCochains DPSimplicialCochainMaps.
Local Open Scope ring_scope.
Module DPSimplicialCochainQuasiIso.
Section Comparison.
Variable R : comPzRingType.
Variable A : lmodType R.
Definition dual_functions (X:simplicial_set) : cochain_map (dual_complex A (chains R X)) (complex X A) :=
 @term_iso_cochain_map R _ _ (@dual_function_iso R X A) (@dual_function_differential R X A).

Lemma dual_functions_pull_square (X Y:simplicial_set) (f:simplicial_map X Y) n
 (a:cochain_term (dual_complex A (chains R Y)) n) :
 cochain_map_at (dual_functions X) n (cochain_map_at (dual_map A (chain_map_of R f)) n a)=
 cochain_map_at (pull f A) n (cochain_map_at (dual_functions Y) n a).
Proof.
apply functional_extensionality_dep=>x.
change (evaluate a (map_at R f n (free_basis R x))=evaluate a (free_basis R (component f n x))).
by rewrite map_at_basis.
Qed.

Lemma dual_function_cohomology_natural (X Y:simplicial_set) (f:simplicial_map X Y) n
 (a:cohomology (dual_complex A (chains R Y)) n) :
 module_hom_fun (iso_hom (dual_function_cohomology_iso X A n))
 (cohomology_map (dual_map A (chain_map_of R f)) n a)=
 cohomology_map (pull f A) n (module_hom_fun (iso_hom (dual_function_cohomology_iso Y A n)) a).
Proof.
exact (@cohomology_map_square R _ _ _ _ (dual_map A (chain_map_of R f)) (pull f A)
 (dual_functions Y) (dual_functions X) (@dual_functions_pull_square X Y f) n a).
Qed.

Variables X Y:simplicial_set.
Variable f:simplicial_map X Y.
Variable hf:quasi_isomorphism (chain_map_of R f).
Definition pull_cohomology_iso n : @isomorphism (module_category R)
 [the lmodType R of cohomology (complex Y A) n] [the lmodType R of cohomology (complex X A) n] :=
 module_iso_comp (iso_symm (dual_function_cohomology_iso Y A n))
 (module_iso_comp (@dual_projective_cohomology_iso R A (chains R X) (chains R Y) (chain_map_of R f)
 (fun n=>@free_projective R (simplex X n)) (fun n=>@free_projective R (simplex Y n)) hf n)
 (dual_function_cohomology_iso X A n)).

Theorem pull_cohomology_iso_forward n (x:cohomology (complex Y A) n) :
 module_hom_fun (iso_hom (pull_cohomology_iso n)) x=cohomology_map (pull f A) n x.
Proof.
change (module_hom_fun (iso_hom (dual_function_cohomology_iso X A n))
 (cohomology_map (dual_map A (chain_map_of R f)) n
 (module_hom_fun (iso_inv (dual_function_cohomology_iso Y A n)) x))=cohomology_map (pull f A) n x).
by rewrite dual_function_cohomology_natural module_iso_inv_hom_apply.
Qed.
End Comparison.
End DPSimplicialCochainQuasiIso.
