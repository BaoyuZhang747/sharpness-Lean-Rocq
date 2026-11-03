From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalCategoryCompact TopologicalSimplexBasic TopologicalSimplexContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalSimplexCompact.
Import DPTopologicalSimplex DPTopologicalSimplexContinuity.
Section Compactness.
Variable Real : realType.

Lemma coordinate_le1 {n} (x : simplex Real n) i : coordinate x i <= 1.
Proof.
have hs := coordinate_sum x; rewrite (bigD1 i) //= in hs.
rewrite -hs lerDl; exact: sumr_ge0 (fun j _ => coordinate_ge0 x j).
Qed.

Lemma vector_sum_continuous n :
  continuous (fun x : 'rV[Real]_n.+1 => \sum_i x ord0 i).
Proof.
apply: continuous_big.
- move=> p; apply: continuousD; [exact: cvg_fst | exact: cvg_snd].
by move=> i _; exact: coord_continuous.
Qed.

Lemma simplex_set_closed n : closed (@simplex_set Real n).
Proof.
have he : @simplex_set Real n =
    (\bigcap_i [set x : 'rV[Real]_n.+1 | 0 <= x ord0 i]) `&`
    [set x : 'rV[Real]_n.+1 | \sum_i x ord0 i = 1].
  apply/seteqP; split=> x [hx hs]; split=> //.
  - by move=> i _; exact: hx.
  - by move=> i; exact: (hx i I).
rewrite he; apply: closedI.
- apply: closed_bigI => i _.
  apply: (@preimage_closed _ _ (fun x : 'rV[Real]_n.+1 => x ord0 i) [set y | 0 <= y]);
    last exact: closed_ge.
  by move=> x _; exact: coord_continuous.
- apply: (@preimage_closed _ _ (fun x : 'rV[Real]_n.+1 => \sum_i x ord0 i) [set y | y = 1]);
    last exact: closed_eq.
  by move=> x _; exact: vector_sum_continuous.
Qed.

Lemma simplex_set_compact n : compact (@simplex_set Real n).
Proof.
have hc : compact [set x : 'rV[Real]_n.+1 | forall i, `[(0 : Real),1]%classic (x ord0 i)].
  apply (@rV_compact _ n.+1 (fun _ => `[(0 : Real),1]%classic)).
  move=> i; exact: segment_compact.
apply (@subclosed_compact _ (@simplex_set Real n) _ (@simplex_set_closed n) hc).
move=> x hx i; rewrite set_itvE /=.
pose sx := @simplex_of_vector Real n x hx.
apply/andP; split; [exact: (coordinate_ge0 sx i) | exact: (coordinate_le1 sx i)].
Qed.

Lemma simplex_compact n : @compact (simplex_space Real n) setT.
Proof. apply: DPTopologicalCompact.compact_subtype; exact: simplex_set_compact. Qed.

End Compactness.
End DPTopologicalSimplexCompact.
