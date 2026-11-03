(** Explicit opaque theorem interfaces for repeated specialisation of the
    genuine pushout proofs; their mathematical hypotheses are unchanged. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout TopologicalPushoutEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module DPTopologicalPushoutEmbeddingOpaque.
Import DPTopological DPCategoryPushout.
Section Actual.
Variables A B X Y : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X)
  (k : hom topological_category B Y) (l : hom topological_category X Y).
Variable h : pushout_square i j k l.
Variable hi : injective i.

Theorem actual_pushout_right_injective : injective l.
Proof. exact (@DPTopologicalPushoutEmbedding.pushout_right_injective A B X Y i j k l h hi). Qed.

Theorem actual_pushout_right_closed
  (hc : forall S : set A, closed S -> closed (i @` S))
  (S : set X) (hS : closed S) : closed (l @` S).
Proof.
exact (@DPTopologicalPushoutEmbedding.pushout_right_closed_image A B X Y i j k l h hi hc S hS).
Qed.

Theorem actual_pushout_accessible
  (hc : forall S : set A, closed S -> closed (i @` S))
  (hB : accessible_space B) (hX : accessible_space X) : accessible_space Y.
Proof.
exact (@DPTopologicalPushoutEmbedding.pushout_accessible A B X Y i j k l h hi hc hB hX).
Qed.
End Actual.
End DPTopologicalPushoutEmbeddingOpaque.
