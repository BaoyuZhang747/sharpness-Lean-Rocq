(** Exactness of actual augmented strings is transported through genuine
    quasi-isomorphisms and actual adjunctions, with degree zero included. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryAdjunction.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism
  CategoryStringChains CategoryStringChainsMaps CategoryStringChainHomotopy
  CategoryInducedBarCofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainQuasiIsomorphism DPCategoryStringChainHomotopy.
Local Open Scope ring_scope.

Module DPCategoryStringExactnessTransport.
Section Transport.
Variable R : pzRingType.
Variables C D : category.
Variable F : functor C D.

Theorem exact_of_quasi_isomorphism
    (hf : quasi_isomorphism (category_string_chain_map R F))
    (hd : category_string_augmented_exact R D) : category_string_augmented_exact R C.
Proof.
split.
- move=> a; have [v hv] := proj1 hd a.
  have [x [hx [w hw]]] := @quasi_iso_cycle_lift R (category_string_chain R C)
    (category_string_chain R D) (category_string_chain_map R F) hf 0%N v I.
  exists x; have he := congr1 (category_string_augmentation R D) hw.
  change (category_string_augmentation R D
    (@category_string_boundary R D 0%N w + category_string_map_at R F 0%N x) =
    category_string_augmentation R D v) in he.
  by rewrite linearD category_string_augmentation_boundary
    category_string_map_augmentation add0r hv in he.
- split.
  + move=> v hv; apply: (@quasi_iso_boundary_reflect R (category_string_chain R C)
      (category_string_chain R D) (category_string_chain_map R F) hf 0%N v I).
    apply (proj1 (proj2 hd)); by rewrite category_string_map_augmentation.
  + move=> n v hv; apply: (@quasi_iso_boundary_reflect R (category_string_chain R C)
      (category_string_chain R D) (category_string_chain_map R F) hf n.+1 v hv).
    apply (proj2 (proj2 hd) n).
    by rewrite category_string_map_boundary hv linear0.
Qed.

Variable G : functor D C.

Lemma exact_of_actual_retract
    (hc : forall n (v : category_string_term R C n), @cycle R (category_string_chain R C) n v ->
      exists w, @category_string_boundary R C n w =
        v - category_string_map_at R (functor_comp F G) n v)
    (hd : category_string_augmented_exact R D) : category_string_augmented_exact R C.
Proof.
split.
- move=> a; have [v hv] := proj1 hd a.
  exists (category_string_map_at R G 0%N v); by rewrite category_string_map_augmentation.
- split.
  + move=> v hv.
    have [w hw] := proj1 (proj2 hd) (category_string_map_at R F 0%N v)
      (eq_trans (@category_string_map_augmentation R C D F v) hv).
    have [z hz] := hc 0%N v I.
    exists (z + category_string_map_at R G 1%N w).
    rewrite linearD.
    change (@category_string_boundary R C 0%N z +
      @category_string_boundary R C 0%N (category_string_map_at R G 1%N w) = v).
    by rewrite hz category_string_map_boundary hw category_string_map_composition subrK.
  + move=> n v hv.
    have hf : @category_string_boundary R D n (category_string_map_at R F n.+1 v) = 0.
      by rewrite category_string_map_boundary hv linear0.
    have [w hw] := proj2 (proj2 hd) n (category_string_map_at R F n.+1 v) hf.
    have [z hz] := hc n.+1 v hv.
    exists (z + category_string_map_at R G n.+2 w).
    rewrite linearD.
    change (@category_string_boundary R C n.+1 z +
      @category_string_boundary R C n.+1 (category_string_map_at R G n.+2 w) = v).
    by rewrite hz category_string_map_boundary hw category_string_map_composition subrK.
Qed.

Theorem exact_of_counit (alpha : nat_trans (functor_comp F G) (functor_id C)) :
  category_string_augmented_exact R D -> category_string_augmented_exact R C.
Proof.
apply exact_of_actual_retract.
move=> n v hv.
have h := chain_homotopy_boundary (category_string_nat_trans_homotopy R alpha) hv.
change (exists w, @category_string_boundary R C n w =
  category_string_map_at R (functor_id C) n v -
    category_string_map_at R (functor_comp F G) n v) in h.
by rewrite category_string_map_identity in h.
Qed.

Theorem exact_of_unit (alpha : nat_trans (functor_id C) (functor_comp F G)) :
  category_string_augmented_exact R D -> category_string_augmented_exact R C.
Proof.
apply exact_of_actual_retract.
move=> n v hv.
have [w hw] := chain_homotopy_boundary (category_string_nat_trans_homotopy R alpha) hv.
change (@category_string_boundary R C n w =
  category_string_map_at R (functor_comp F G) n v -
    category_string_map_at R (functor_id C) n v) in hw.
exists (-w); rewrite linearN.
change (- @category_string_boundary R C n w =
  v - category_string_map_at R (functor_comp F G) n v).
by rewrite hw category_string_map_identity opprB.
Qed.

Theorem exact_left_of_adjunction (a : adjunction F G) :
  category_string_augmented_exact R D -> category_string_augmented_exact R C.
Proof. exact (exact_of_unit (adj_unit a)). Qed.

Theorem exact_right_of_adjunction (a : adjunction G F) :
  category_string_augmented_exact R D -> category_string_augmented_exact R C.
Proof. exact (exact_of_counit (adj_counit a)). Qed.
End Transport.
End DPCategoryStringExactnessTransport.

Print Assumptions DPCategoryStringExactnessTransport.exact_of_quasi_isomorphism.
Print Assumptions DPCategoryStringExactnessTransport.exact_left_of_adjunction.
Print Assumptions DPCategoryStringExactnessTransport.exact_right_of_adjunction.
