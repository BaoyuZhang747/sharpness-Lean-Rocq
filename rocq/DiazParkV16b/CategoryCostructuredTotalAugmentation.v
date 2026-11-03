(** The literal total augmentation for the costructured replacement is a quasi-isomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryComma BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialSet SimplicialChains SimplicialChainsMaps CategoryNerve
 BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyNaturality FirstQuadrantChainTotalMaps FirstQuadrantChainFlipComparison
 SimplicialReplacementConstants SimplicialReplacementTypes SimplicialReplacement CategoryCostructuredDiagram CategoryCostructuredReplacementRows CategoryCostructuredReplacementRowMaps CategoryCostructuredRowAugmentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPCategoryNerve
 DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyNaturality DPSimplicialReplacementConstants DPSimplicialReplacementTypes DPSimplicialReplacement DPCategoryCostructuredDiagram DPCategoryCostructuredReplacementRows DPCategoryCostructuredReplacementRowMaps DPCategoryCostructuredRowAugmentation.
Local Open Scope ring_scope.
Module DPCategoryCostructuredTotalAugmentation.
Section Total.
Variable R : pzRingType.
Variables C D : category.
Variable T : functor C D.
Local Notation F := (costructured_nerve_diagram T).
Definition row_augmentation q := DPFirstQuadrantChainTotalMaps.horizontal_map (bisimplicial_chain_map R (costructured_augmentation T)) q.
Lemma row_augmentation_formula q n (x:term R (horizontal_simplicial (replacement F) q) n) :
 chain_map_at (row_augmentation q) n x=map_at R (row_projection T q) n (map_at R (row_forward_map T q) n x).
Proof.
apply (free_lift_ext
 (g := chain_map_at (row_augmentation q) n)
 (h := (map_at R (row_projection T q) n \o map_at R (row_forward_map T q) n : {linear _ -> _}))).
move=>[d s].
change (free_map R (bisimplex_component (costructured_augmentation T) n q) (free_basis R (existT _ d s))=
 map_at R (row_projection T q) n (map_at R (row_forward_map T q) n (free_basis R (existT _ d s)))).
by rewrite free_map_basis !map_at_basis.
Qed.
Definition row_source_bridge q : chain_map
 (DPFirstQuadrantChainTotalMaps.horizontal_complex (bisimplicial_bicomplex R (replacement F)) q)
 (chains R (horizontal_simplicial (replacement F) q)).
Proof.
refine (@ChainMap R (DPFirstQuadrantChainTotalMaps.horizontal_complex (bisimplicial_bicomplex R (replacement F)) q)
 (chains R (horizontal_simplicial (replacement F) q)) (fun n=>(idfun : {linear _ -> _})) _).
move=>n x; reflexivity. Defined.
Definition row_target_bridge q : chain_map
 (DPFirstQuadrantChainTotalMaps.horizontal_complex (bisimplicial_bicomplex R (horizontal_constant (nerve C))) q)
 (chains R (constant_simplicial (simplex (nerve C) q))).
Proof.
refine (@ChainMap R (DPFirstQuadrantChainTotalMaps.horizontal_complex (bisimplicial_bicomplex R (horizontal_constant (nerve C))) q)
 (chains R (constant_simplicial (simplex (nerve C) q))) (fun n=>(idfun : {linear _ -> _})) _).
move=>n x; reflexivity. Defined.
Lemma row_source_bridge_quasi q : quasi_isomorphism (row_source_bridge q).
Proof.
apply degreewise_bijective_quasi_isomorphism.
- move=>n x y h; exact h.
- move=>n y; exists y; reflexivity.
Qed.
Lemma row_target_bridge_quasi q : quasi_isomorphism (row_target_bridge q).
Proof.
apply degreewise_bijective_quasi_isomorphism.
- move=>n x y h; exact h.
- move=>n y; exists y; reflexivity.
Qed.
Lemma row_augmentation_quasi_isomorphism q : quasi_isomorphism (row_augmentation q).
Proof.
apply (@quasi_isomorphism_cancel_second R _ _ _ (row_augmentation q) (row_target_bridge q)); first exact: row_target_bridge_quasi.
apply (@quasi_isomorphism_ext R _ _
 (chain_composition (row_source_bridge q)
 (chain_composition (chain_map_of R (row_forward_map T q)) (chain_map_of R (row_projection T q))))
 (chain_composition (row_augmentation q) (row_target_bridge q))).
- move=>n x; symmetry; exact: row_augmentation_formula.
- apply quasi_isomorphism_composition; first exact: row_source_bridge_quasi.
  apply quasi_isomorphism_composition; [exact: row_forward_quasi_isomorphism | exact: row_projection_quasi_isomorphism].
Qed.
Theorem total_augmentation_quasi_isomorphism : quasi_isomorphism (total_chains_map R (costructured_augmentation T)).
Proof. exact: DPFirstQuadrantChainFlipComparison.row_total_map_quasi_isomorphism row_augmentation_quasi_isomorphism. Qed.
End Total.
End DPCategoryCostructuredTotalAugmentation.
