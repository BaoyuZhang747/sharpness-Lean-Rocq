(** Connectedness of the actual standard simplex, through its actual straight-line paths. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic TopologicalSimplexContinuity TopologicalSimplexContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopological DPTopologicalHomotopy DPTopologicalSimplex
  DPTopologicalSimplexContinuity DPTopologicalSimplexContraction.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalSimplexConnected.

Lemma connected_subtype (X : topologicalType) (A : set X) (a : set_type A) :
  connected A -> @connected [the topologicalType of set_type A] setT.
Proof.
move=> hA.
pose f := valL_ a (@id (set_type A)).
have hf : {within A, continuous f}.
  apply: (proj2 (@subspace_valL_continuousP' X A
    [the topologicalType of set_type A] a (@id (set_type A)))).
  by move=> x; exact: cvg_id.
have he : f @` A = setT.
  apply/seteqP; split=> x _ //.
  exists (val x); first exact: set_valP.
  exact: (congr1 (fun g => g x) (valLK a (@id (set_type A)))).
rewrite -he; exact: connected_continuous_connected hA hf.
Qed.

Lemma unit_interval_connected (Real : realType) :
  @connected (unit_interval_space Real) setT.
Proof.
apply: (@connected_subtype Real (@unit_interval_set Real) (interval_zero Real)).
have e : @unit_interval_set Real = `[0, 1].
  apply/seteqP; split=> x hx; by rewrite /unit_interval_set /= in_itv /= in hx |- *.
rewrite e; exact: segment_connected.
Qed.

Definition simplex_path (Real : realType) n (x y : simplex Real n) :
    continuousType (unit_interval_space Real) (simplex_space Real n).
Proof.
apply: (@continuous_map _ _ (fun t => mix t x y)).
move=> t; apply: (@continuous_comp _ [the topologicalType of
  (unit_interval_space Real * simplex_space Real n)%type] _
  (fun s => (s,x)) (fun p => mix p.1 p.2 y) t).
- apply: (@cvg_pair _ (unit_interval_space Real) (simplex_space Real n)
    (nbhs t) (nbhs t) (nbhs x) (@nbhs_filter (unit_interval_space Real) t)
    (@nbhs_filter (unit_interval_space Real) t) (@nbhs_filter (simplex_space Real n) x));
    [exact: cvg_id | exact: cvg_cst].
- exact: mix_continuous.
Defined.

Lemma simplex_connected (Real : realType) n :
  @connected (simplex_space Real n) setT.
Proof.
pose y := @vertex Real n ord0.
pose A (x : simplex_space Real n) := simplex_path x y @` setT.
have he : setT = \bigcup_x A x.
  apply/seteqP; split=> x _ //.
  exists x => //; exists (interval_zero Real) => //; exact: mix_start.
rewrite he; apply: bigcup_connected.
- exists y => x _; exists (interval_one Real) => //; exact: mix_end.
- move=> x _; apply: connected_continuous_connected.
  + exact: unit_interval_connected.
  + apply: continuous_subspaceT; exact: cts_fun.
Qed.

End DPTopologicalSimplexConnected.
