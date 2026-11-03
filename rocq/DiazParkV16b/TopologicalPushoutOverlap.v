(** Literal overlap homeomorphism obtained by restricting the actual complement map. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout
  TopologicalPushoutComplement TopologicalHomeomorphismSubspaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPCategoryPushout DPTopologicalPushoutComplement
  DPTopologicalHomeomorphismSubspaces.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutOverlap.

Definition homeomorphism_compose {X Y Z : topologicalType}
    (e : homeomorphism X Y) (f : homeomorphism Y Z) : homeomorphism X Z.
Proof.
refine (@Build_isomorphism topological_category X Z
  (continuous_compose (iso_hom e) (iso_hom f))
  (continuous_compose (iso_inv f) (iso_inv e)) _ _).
- apply: topological_hom_ext => x.
  change (iso_inv e (iso_inv f (iso_hom f (iso_hom e x))) = x).
  by rewrite !homeomorphism_forwardK.
- apply: topological_hom_ext => z.
  change (iso_hom f (iso_hom e (iso_inv e (iso_inv f z))) = z).
  by rewrite !homeomorphism_inverseK.
Defined.

Section Overlap.
Variables A B X Y : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X)
  (k : hom topological_category B Y) (l : hom topological_category X Y).
Variable h : pushout_square i j k l.
Variable hi : injective i.
Variable hi_closed : forall S : set A, closed S -> closed (i @` S).
Variables (N : set B) (M : set Y).
Variable hNM : forall b, N b <-> M (k b).

Let e := @pushout_complement_homeomorphism A B X Y i j k l h hi hi_closed.
Let source_set := @source_complement A B i.
Let target_set := @target_complement X Y l.
Let Ns : set (@source_complement_space A B i) := fun b => N (val b).
Let Mt : set (@target_complement_space X Y l) := fun y => M (val y).

Lemma complement_overlap_correspondence b : Ns b <-> Mt (iso_hom e b).
Proof. exact: hNM. Qed.

Definition pushout_overlap_homeomorphism : homeomorphism
    (@intersection_space B source_set N) (@intersection_space Y target_set M) :=
  homeomorphism_compose
    (homeomorphism_compose (@intersection_nested_homeomorphism B source_set N)
      (@restricted_homeomorphism _ _ e Ns Mt complement_overlap_correspondence))
    (iso_symm (@intersection_nested_homeomorphism Y target_set M)).

Theorem pushout_overlap_homeomorphism_val b :
  val (iso_hom pushout_overlap_homeomorphism b) = k (val b).
Proof. reflexivity. Qed.

End Overlap.
End DPTopologicalPushoutOverlap.
