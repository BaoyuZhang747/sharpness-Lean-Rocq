From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic TopologicalSimplexContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalSimplexContraction.
Import DPTopological DPTopologicalHomotopy DPTopologicalSimplex
  DPTopologicalSimplexContinuity.
Section Contraction.
Variable Real : realType.

Definition mix_vector {n} (t : unit_interval Real) (x y : simplex Real n) :=
  (1 - val t) *: simplex_vector x + val t *: simplex_vector y.

Lemma mix_vector_coordinate {n} (t : unit_interval Real) (x y : simplex Real n) i :
  mix_vector t x y ord0 i = (1 - val t) * coordinate x i + val t * coordinate y i.
Proof. by rewrite /mix_vector !mxE. Qed.

Lemma mix_vector_in {n} (t : unit_interval Real) (x y : simplex Real n) :
  @simplex_set Real n (mix_vector t x y).
Proof.
split.
- move=> i; rewrite mix_vector_coordinate; apply: addr_ge0.
  + apply: mulr_ge0; last exact: coordinate_ge0.
    by rewrite subr_ge0; exact: interval_le1.
  + apply: mulr_ge0; [exact: interval_ge0 | exact: coordinate_ge0].
- under eq_bigr do rewrite mix_vector_coordinate.
  rewrite big_split -!mulr_sumr !coordinate_sum !mulr1.
  change ((1 - val t) + val t = 1).
  by rewrite subrK.
Qed.

Definition mix {n} (t : unit_interval Real) (x y : simplex Real n) : simplex Real n :=
  simplex_of_vector (mix_vector_in t x y).

Lemma mix_start {n} (x y : simplex Real n) : mix (interval_zero Real) x y = x.
Proof.
apply: val_inj; change ((1 - 0) *: simplex_vector x + 0 *: simplex_vector y = simplex_vector x).
by rewrite subr0 scale1r scale0r addr0.
Qed.

Lemma mix_end {n} (x y : simplex Real n) : mix (interval_one Real) x y = y.
Proof.
apply: val_inj; change ((1 - 1) *: simplex_vector x + 1 *: simplex_vector y = simplex_vector y).
by rewrite subrr scale0r scale1r add0r.
Qed.

Lemma mix_fixed {n} (t : unit_interval Real) (x : simplex Real n) : mix t x x = x.
Proof.
apply: val_inj; change ((1 - val t) *: simplex_vector x + val t *: simplex_vector x = simplex_vector x).
by rewrite -scalerDl subrK scale1r.
Qed.

Lemma mix_continuous {n} (y : simplex Real n) :
  continuous (fun p : (unit_interval_space Real * simplex_space Real n)%type => mix p.1 p.2 y).
Proof.
apply: (@continuous_comp_initial _ _ _ set_val).
move=> p.
change {for p, continuous (fun q : (unit_interval_space Real * simplex_space Real n)%type =>
  (1 - val q.1) *: simplex_vector q.2 + val q.1 *: simplex_vector y)}.
apply: continuousD.
- apply: continuousZ.
  + apply: continuousB; first exact: cst_continuous.
    apply: (@continuous_comp _ (unit_interval_space Real) _
      (fun q : (unit_interval_space Real * simplex_space Real n)%type => q.1)
      (fun t : unit_interval Real => val t) p);
      [exact: cvg_fst | exact: initial_continuous].
  + apply: (@continuous_comp _ (simplex_space Real n) _
      (fun q : (unit_interval_space Real * simplex_space Real n)%type => q.2)
      (@simplex_vector Real n) p);
      [exact: cvg_snd | exact: simplex_vector_continuous].
- apply: continuousZ.
  + apply: (@continuous_comp _ (unit_interval_space Real) _
      (fun q : (unit_interval_space Real * simplex_space Real n)%type => q.1)
      (fun t : unit_interval Real => val t) p);
      [exact: cvg_fst | exact: initial_continuous].
  + exact: cst_continuous.
Qed.

Definition simplex_contraction {n} (y : simplex Real n) :
    continuous_homotopy Real (continuous_identity (simplex_space Real n))
      [the continuousType (simplex_space Real n) (simplex_space Real n) of (cst y)].
Proof.
refine (@ContinuousHomotopy Real _ _ _ _ (continuous_map (@mix_continuous n y)) _ _).
- move=> x; change (mix (interval_zero Real) x y = x); exact: mix_start.
- move=> x; change (mix (interval_one Real) x y = y); exact: mix_end.
Defined.

End Contraction.
End DPTopologicalSimplexContraction.
