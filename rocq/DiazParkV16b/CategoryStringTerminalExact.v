(** Exact augmented strings of a category with an actual terminal object. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryLimits.
From DiazParkV16b Require Import CategoryStringConstantChains CategoryStringContraction
  CategoryInducedBarCofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryStringTerminalExact.
Section Terminal.
Variable C : category.
Variable t : terminal_object C.
Let K := DPCategoryStringConstant.constant_functor C (terminal_point t).

Definition terminal_transformation : nat_trans (functor_id C) K.
Proof.
refine (@Build_nat_trans C C (functor_id C) K (terminal_arrow t) _).
intros x y f; transitivity (terminal_arrow t x).
- apply terminal_unique.
- symmetry; apply terminal_unique.
Defined.

Definition constant_identity : nat_trans K K.
Proof.
refine (@Build_nat_trans C C K K (fun _ => identity (terminal_point t)) _).
intros; by rewrite !compose_id_left.
Defined.

Theorem terminal_augmented_exact (R : pzRingType) : category_string_augmented_exact R C.
Proof.
exact (@DPCategoryStringContraction.category_string_augmented_exact_of_contraction
  R C (terminal_point t) K terminal_transformation constant_identity).
Qed.
End Terminal.
End DPCategoryStringTerminalExact.
