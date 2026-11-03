(** Literal functor-map quasi-isomorphisms agree in native nerve and string chains. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws
  SimplicialChains SimplicialChainsMaps CategoryNerve CategoryStringChains CategoryStringChainsMaps
  CategoryNerveStringChainTerms CategoryNerveStringChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPSimplicialChains DPSimplicialChainMaps DPCategoryNerve.

Module DPCategoryQuillenANerveString.
Section Comparison.
Variable R : pzRingType.

Lemma nerve_to_string_quasi_isomorphism (C : category) :
  quasi_isomorphism (nerve_to_string_chain R C).
Proof.
apply degreewise_bijective_quasi_isomorphism.
- move=> n; exact (can_inj (@string_to_nerve_inverse R C n)).
- move=> n x; exists (string_to_nerve_at R C n x); exact: nerve_to_string_inverse.
Qed.

Variables C D : category.
Variable T : functor C D.

Theorem string_quasi_isomorphism_of_nerve :
  quasi_isomorphism (chain_map_of R (nerve_map T)) ->
  quasi_isomorphism (category_string_chain_map R T).
Proof.
move=> h.
apply: (quasi_isomorphism_cancel_first (f := nerve_to_string_chain R C)).
- exact: nerve_to_string_quasi_isomorphism.
- apply: (quasi_isomorphism_ext
    (f := chain_composition (chain_map_of R (nerve_map T)) (nerve_to_string_chain R D))).
  + move=> n x; exact: nerve_to_string_naturality.
  + apply quasi_isomorphism_composition; [exact h | exact: nerve_to_string_quasi_isomorphism].
Qed.

Theorem nerve_quasi_isomorphism_of_string :
  quasi_isomorphism (category_string_chain_map R T) ->
  quasi_isomorphism (chain_map_of R (nerve_map T)).
Proof.
move=> h.
apply: (quasi_isomorphism_cancel_second (g := nerve_to_string_chain R D)).
- exact: nerve_to_string_quasi_isomorphism.
- apply: (quasi_isomorphism_ext
    (f := chain_composition (nerve_to_string_chain R C) (category_string_chain_map R T))).
  + move=> n x; symmetry; exact: nerve_to_string_naturality.
  + apply quasi_isomorphism_composition; [exact: nerve_to_string_quasi_isomorphism | exact h].
Qed.

Theorem nerve_string_quasi_isomorphism_iff :
  quasi_isomorphism (chain_map_of R (nerve_map T)) <->
  quasi_isomorphism (category_string_chain_map R T).
Proof. split; [exact string_quasi_isomorphism_of_nerve | exact nerve_quasi_isomorphism_of_string]. Qed.
End Comparison.
End DPCategoryQuillenANerveString.
