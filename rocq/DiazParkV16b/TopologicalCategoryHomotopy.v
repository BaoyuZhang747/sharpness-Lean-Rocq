From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalHomotopy.
Import DPTopological.
Section Interval.
Variable Real : realType.

Definition unit_interval_set : set Real := [set t | 0 <= t <= 1].
Definition unit_interval := set_type unit_interval_set.
Definition unit_interval_space : topologicalType :=
  [the topologicalType of set_type unit_interval_set].

Lemma unit_interval_zero_in : unit_interval_set 0.
Proof. by rewrite /unit_interval_set /= lexx ler01. Qed.
Lemma unit_interval_one_in : unit_interval_set 1.
Proof. by rewrite /unit_interval_set /= ler01 lexx. Qed.

Definition interval_zero : unit_interval := exist _ 0 (mem_set unit_interval_zero_in).
Definition interval_one : unit_interval := exist _ 1 (mem_set unit_interval_one_in).

Lemma interval_ge0 (t : unit_interval) : 0 <= val t.
Proof. by have /andP[] := set_valP t. Qed.
Lemma interval_le1 (t : unit_interval) : val t <= 1.
Proof. by have /andP[] := set_valP t. Qed.
Lemma interval_val_continuous : continuous (@set_val Real unit_interval_set).
Proof. exact: initial_continuous. Qed.

Record continuous_homotopy {X Y : topologicalType}
    (f g : continuousType X Y) := ContinuousHomotopy {
  homotopy_map : continuousType (unit_interval_space * X)%type Y;
  homotopy_start : forall x, homotopy_map (interval_zero, x) = f x;
  homotopy_end : forall x, homotopy_map (interval_one, x) = g x
}.

End Interval.
End DPTopologicalHomotopy.
