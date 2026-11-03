(** Native augmented exactness is invariant under taking the opposite category. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category.
From DiazParkV16b Require Import CategoryStringChains CategoryStringOppositeChains CategoryInducedBarCofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPCategoryStringOppositeChains.
Local Open Scope ring_scope.

Module DPCategoryStringOppositeExact.
Section Exact.
Variable R : pzRingType.
Variable C : category.

Theorem augmented_exact_opposite : category_string_augmented_exact R C ->
  category_string_augmented_exact R (opposite C).
Proof.
move=> h; split.
- move=> a; have [v hv] := proj1 h a.
  exists (reverse_at R C 0%N v); by rewrite reverse_augmentation.
- split.
  + move=> v hv.
    have hu : category_string_augmentation R C (unreverse_at R C 0%N v) = 0.
      by rewrite unreverse_augmentation.
    have [w hw] := proj1 (proj2 h) _ hu.
    exists (reverse_at R C 1%N w); by rewrite reverse_boundary hw unreverse_inverse.
  + move=> n v hv.
    have hu : @category_string_boundary R C n (unreverse_at R C n.+1 v) = 0.
      by rewrite unreverse_boundary hv linear0.
    have [w hw] := proj2 (proj2 h) _ _ hu.
    exists (reverse_at R C n.+2 w); by rewrite reverse_boundary hw unreverse_inverse.
Qed.

Theorem augmented_exact_unopposite : category_string_augmented_exact R (opposite C) ->
  category_string_augmented_exact R C.
Proof.
move=> h; split.
- move=> a; have [v hv] := proj1 h a.
  exists (unreverse_at R C 0%N v); by rewrite unreverse_augmentation.
- split.
  + move=> v hv.
    have hu : category_string_augmentation R (opposite C) (reverse_at R C 0%N v) = 0.
      by rewrite reverse_augmentation.
    have [w hw] := proj1 (proj2 h) _ hu.
    exists (unreverse_at R C 1%N w); by rewrite unreverse_boundary hw reverse_inverse.
  + move=> n v hv.
    have hu : @category_string_boundary R (opposite C) n (reverse_at R C n.+1 v) = 0.
      by rewrite reverse_boundary hv linear0.
    have [w hw] := proj2 (proj2 h) _ _ hu.
    exists (unreverse_at R C n.+2 w); by rewrite unreverse_boundary hw reverse_inverse.
Qed.

Theorem augmented_exact_opposite_iff : category_string_augmented_exact R C <->
  category_string_augmented_exact R (opposite C).
Proof. split; [exact augmented_exact_opposite | exact augmented_exact_unopposite]. Qed.
End Exact.
End DPCategoryStringOppositeExact.
