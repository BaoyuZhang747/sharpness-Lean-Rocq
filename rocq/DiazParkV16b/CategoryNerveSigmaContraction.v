(** Actual homology equivalence from a disjoint family of contracted category nerves to its index set. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryReindex MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve ChainComplex ChainHomology ChainHomologyMaps ChainQuasiIsomorphism
 SimplicialChains SimplicialChainsMaps SimplicialChainHomologyLaws CategoryStringConstantChains CategoryNerveNatTransHomotopy SimplicialSigma SimplicialSigmaHomotopy SimplicialReplacementConstants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism
 DPSimplicialChains DPSimplicialChainMaps DPSimplicialChainHomologyLaws DPCategoryStringConstant DPCategoryNerveNatTransHomotopy DPSimplicialSigma DPSimplicialSigmaHomotopy DPSimplicialReplacementConstants.
Local Open Scope ring_scope.
Module DPCategoryNerveSigmaContraction.
Section Contraction.
Variable I : Type.
Variable C : I -> category.
Variable b : forall i,C i.
Variable a : forall i,nat_trans (@constant_diagram (C i) (C i) (b i)) (functor_id (C i)).
Local Notation X := (fun i=>nerve (C i)).
Definition nerve_sigma_section : simplicial_map (constant_simplicial I) (sigma_set X).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (constant_simplicial I) (sigma_set X)
 (fun n i=>existT _ i (@constant_diagram (ordinal_category n) (C i) (b i))) _).
move=>n m f; apply type_morphism_ext=>i.
congr (existT _ i _).
change (@constant_diagram (ordinal_category m) (C i) (b i)=
 functor_comp (ordinal_functor f) (@constant_diagram (ordinal_category n) (C i) (b i))).
apply (@functor_ext_pointwise _ _ (@constant_diagram (ordinal_category m) (C i) (b i))
 (functor_comp (ordinal_functor f) (@constant_diagram (ordinal_category n) (C i) (b i))) (fun j=>Logic.eq_refl _)).
move=>j k u; reflexivity.
Defined.
Lemma projection_section : nat_comp nerve_sigma_section (sigma_projection X)=nat_id (constant_simplicial I).
Proof. apply nat_trans_ext=>n; apply type_morphism_ext=>i; reflexivity. Qed.
Lemma sigma_nerve_identity : sigma_map (fun i=>nerve_map (functor_id (C i)))=nat_id (sigma_set X).
Proof.
apply nat_trans_ext=>n; apply type_morphism_ext=>[[i s]].
change (@existT I (fun j=>simplex (nerve (C j)) n) i (functor_comp s (functor_id (C i)))=existT _ i s).
by rewrite functor_comp_id_right.
Qed.
Lemma sigma_nerve_constant : sigma_map (fun i=>nerve_map (@constant_diagram (C i) (C i) (b i)))=
 nat_comp (sigma_projection X) nerve_sigma_section.
Proof.
apply nat_trans_ext=>n; apply type_morphism_ext=>[[i s]].
change (@existT I (fun j=>simplex (nerve (C j)) n) i (functor_comp s (@constant_diagram (C i) (C i) (b i)))=
 existT _ i (@constant_diagram (ordinal_category n) (C i) (b i))).
congr (existT _ i _).
apply (@functor_ext_pointwise _ _ (functor_comp s (@constant_diagram (C i) (C i) (b i)))
 (@constant_diagram (ordinal_category n) (C i) (b i)) (fun j=>Logic.eq_refl _)).
move=>j k u; reflexivity.
Qed.
Variable R : pzRingType.
Lemma nerve_sigma_homology_left n (x:homology (chains R (sigma_set X)) n) :
 homology_map (chain_map_of R nerve_sigma_section) n (homology_map (chain_map_of R (sigma_projection X)) n x)=x.
Proof.
pose h := @sigma_chain_homotopy R I X X (fun i=>nerve_map (functor_id (C i)))
 (fun i=>nerve_map (@constant_diagram (C i) (C i) (b i)))
 (fun i=>@nerve_nat_trans_homotopy R (C i) (C i) (@constant_diagram (C i) (C i) (b i)) (functor_id (C i)) (a i)).
have hh := homology_map_homotopy h x.
rewrite sigma_nerve_identity sigma_nerve_constant simplicial_homology_identity simplicial_homology_composition in hh.
exact (Logic.eq_sym hh).
Qed.
Lemma nerve_sigma_homology_right n (x:homology (chains R (constant_simplicial I)) n) :
 homology_map (chain_map_of R (sigma_projection X)) n (homology_map (chain_map_of R nerve_sigma_section) n x)=x.
Proof. by rewrite -simplicial_homology_composition projection_section simplicial_homology_identity. Qed.
Theorem nerve_sigma_projection_quasi_isomorphism : quasi_isomorphism (chain_map_of R (sigma_projection X)).
Proof.
move=>n; split.
- move=>x y hxy; rewrite -(nerve_sigma_homology_left x) -(nerve_sigma_homology_left y) hxy; reflexivity.
- move=>y; exists (homology_map (chain_map_of R nerve_sigma_section) n y); exact: nerve_sigma_homology_right.
Qed.
End Contraction.
End DPCategoryNerveSigmaContraction.
