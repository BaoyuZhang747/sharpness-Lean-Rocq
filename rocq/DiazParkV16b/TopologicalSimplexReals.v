From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals Rstruct topology normedtype matrix_normedtype subtype_topology.
From Stdlib Require Import Reals.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic TopologicalSimplexAffine TopologicalSimplexContinuity
  TopologicalSimplexOrdinal TopologicalSimplexCompact TopologicalSimplexContraction
  TopologicalSimplexFaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** This concrete bridge uses the pinned Stdlib real construction and Rstruct.
    Its additional named logical dependencies are audited separately; they are
    not hidden as assumptions about geometry. *)
Module DPStandardSimplex.
Import DPTopological DPTopologicalHomotopy DPTopologicalSimplex
  DPTopologicalSimplexOrdinal DPTopologicalSimplexCompact
  DPTopologicalSimplexContraction DPTopologicalSimplexFaces.

Definition real_line : realType := [the realType of (R : Type)].
Definition standard_simplex n := simplex_space real_line n.
Definition standard_simplex_functor := topological_simplex_functor real_line.

Lemma standard_simplex_compact n : @compact.compact (standard_simplex n) setT.
Proof. exact: simplex_compact. Qed.

Definition standard_simplex_contraction n (y : standard_simplex n) :=
  simplex_contraction y.

Definition standard_simplex_zero_homeomorphism := simplex_zero_homeomorphism real_line.

Lemma standard_boundary_compact n :
  @compact.compact (boundary_space real_line n) setT.
Proof. exact: boundary_compact. Qed.

End DPStandardSimplex.
