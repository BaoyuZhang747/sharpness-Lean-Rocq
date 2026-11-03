(** Actual compactness and separation of the interval used by continuous homotopies. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalCategoryHomotopy TopologicalCategoryCompact
  GeometricRealizationBoundaryTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports
  DPTopologicalHomotopy DPTopologicalCompact DPRealizationBoundaryTopology.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalHomotopyInterval.
Section Interval.
Variable Real : realType.

Lemma unit_interval_compact : @compact (unit_interval_space Real) setT.
Proof.
apply: compact_subtype.
have e : @unit_interval_set Real = `[0, 1].
  apply/seteqP; split=> x hx; by rewrite /unit_interval_set /= in_itv /= in hx |- *.
rewrite e; exact: segment_compact.
Qed.

Lemma unit_interval_hausdorff : hausdorff_space (unit_interval_space Real).
Proof. apply: subtype_hausdorff; exact: norm_hausdorff. Qed.

Lemma unit_interval_locally_compact : @locally_compact (unit_interval_space Real) setT.
Proof.
move=> x _; exists setT.
- exact: filterT.
- split; [exact: unit_interval_compact | exact: closedT].
Qed.

End Interval.
End DPTopologicalHomotopyInterval.

