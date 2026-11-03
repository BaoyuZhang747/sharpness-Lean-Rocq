(** Quasi-isomorphisms of actual functor-induced string maps are opposite-invariant. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws
  CategoryStringChains CategoryStringChainsMaps CategoryStringOppositeChains CategoryStringOppositeNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPCategoryStringOppositeChains DPCategoryStringOppositeNaturality.

Module DPCategoryStringOppositeQuasiIso.
Section QuasiIso.
Variable R : pzRingType.

Lemma reverse_quasi_isomorphism (C : category) : quasi_isomorphism (reverse_chain R C).
Proof.
apply degreewise_bijective_quasi_isomorphism.
- move=> n; exact (can_inj (@reverse_inverse R C n)).
- move=> n v; exists (unreverse_at R C n v); exact: unreverse_inverse.
Qed.

Lemma unreverse_quasi_isomorphism (C : category) : quasi_isomorphism (unreverse_chain R C).
Proof.
apply degreewise_bijective_quasi_isomorphism.
- move=> n; exact (can_inj (@unreverse_inverse R C n)).
- move=> n v; exists (reverse_at R C n v); exact: reverse_inverse.
Qed.

Variables C D : category.
Variable F : functor C D.

Theorem functor_map_opposite_quasi_isomorphism :
  quasi_isomorphism (category_string_chain_map R F) ->
  quasi_isomorphism (category_string_chain_map R (functor_op F)).
Proof.
move=> h.
apply: (quasi_isomorphism_cancel_first (f := reverse_chain R C)).
- exact: reverse_quasi_isomorphism.
- apply: (quasi_isomorphism_ext
    (f := chain_composition (category_string_chain_map R F) (reverse_chain R D))).
  + move=> n v; exact: reverse_naturality.
  + apply quasi_isomorphism_composition; [exact h | exact: reverse_quasi_isomorphism].
Qed.

Theorem functor_map_unopposite_quasi_isomorphism :
  quasi_isomorphism (category_string_chain_map R (functor_op F)) ->
  quasi_isomorphism (category_string_chain_map R F).
Proof.
move=> h.
apply: (quasi_isomorphism_cancel_first (f := unreverse_chain R C)).
- exact: unreverse_quasi_isomorphism.
- apply: (quasi_isomorphism_ext
    (f := chain_composition (category_string_chain_map R (functor_op F)) (unreverse_chain R D))).
  + move=> n v; exact: unreverse_naturality.
  + apply quasi_isomorphism_composition; [exact h | exact: unreverse_quasi_isomorphism].
Qed.

Theorem functor_map_opposite_quasi_isomorphism_iff :
  quasi_isomorphism (category_string_chain_map R F) <->
  quasi_isomorphism (category_string_chain_map R (functor_op F)).
Proof. split; [exact functor_map_opposite_quasi_isomorphism | exact functor_map_unopposite_quasi_isomorphism]. Qed.
End QuasiIso.
End DPCategoryStringOppositeQuasiIso.
