From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalConnecting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalConnecting.
Local Open Scope ring_scope.

Section ExactAcyclicity.
Variable R : pzRingType.
Variables A B C : @cochain_complex R.
Variables (f : cochain_map A B) (g : cochain_map B C).
Variable s : degreewise_short_exact f g.

Lemma quotient_cohomology_zero n :
  (forall q : cohomology A n.+1, q = 0) ->
  (forall q : cohomology B n, q = 0) -> forall q : cohomology C n, q = 0.
Proof.
move=> hA hB q.
have [r hr] := proj1 (connecting_map_kernel s q) (hA (connecting_map s n q)).
by rewrite -hr (hB r) linear0.
Qed.

Theorem positive_acyclic_quotient_iff : positive_acyclic A ->
  (positive_acyclic B <-> positive_acyclic C).
Proof.
move=> hA; split.
- move=> hB; apply/positive_acyclic_cohomology => n.
  apply (@quotient_cohomology_zero n.+1).
  + exact (proj1 (positive_acyclic_cohomology A) hA n.+1).
  + exact (proj1 (positive_acyclic_cohomology B) hB n).
- exact: positive_acyclic_extension s hA.
Qed.

Theorem all_degree_acyclic_quotient_iff : all_degree_acyclic A ->
  (all_degree_acyclic B <-> all_degree_acyclic C).
Proof.
move=> hA; split.
- move=> hB; apply/all_degree_acyclic_cohomology => n.
  apply (@quotient_cohomology_zero n).
  + exact (proj1 (all_degree_acyclic_cohomology A) hA n.+1).
  + exact (proj1 (all_degree_acyclic_cohomology B) hB n).
- exact: all_degree_acyclic_extension s hA.
Qed.

End ExactAcyclicity.
