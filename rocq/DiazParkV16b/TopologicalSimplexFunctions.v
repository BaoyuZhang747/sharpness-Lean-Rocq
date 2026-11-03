(** Barycentric scalar functions on the actual standard topological simplex. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic TopologicalSimplexAffine TopologicalSimplexContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopologicalSimplex DPTopologicalSimplexAffine DPTopologicalSimplexContinuity
  DPTopologicalHomotopy.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalSimplexFunctions.
Section Scalar.
Variable Real : realType.

Definition weighted_value {n} (w : 'I_n.+1 -> Real) (x : simplex Real n) :=
  \sum_i coordinate x i * w i.

Lemma weighted_constant n (c : Real) (x : simplex Real n) :
  weighted_value (fun _ => c) x = c.
Proof. by rewrite /weighted_value -mulr_suml coordinate_sum mul1r. Qed.

Lemma weighted_vertex n (w : 'I_n.+1 -> Real) (i : 'I_n.+1) :
  weighted_value w (@vertex Real n i) = w i.
Proof.
rewrite /weighted_value (bigD1 i) // coordinate_vertex eqxx mul1r /=.
have -> : \sum_(j | j != i) coordinate (@vertex Real n i) j * w j = 0.
  by apply big1 => j hj; rewrite coordinate_vertex (negbTE hj) mul0r.
by rewrite addr0.
Qed.

Lemma weighted_pushforward n m (f : 'I_n.+1 -> 'I_m.+1)
    (w : 'I_m.+1 -> Real) (x : simplex Real n) :
  weighted_value w (pushforward f x) = weighted_value (w \o f) x.
Proof.
rewrite /weighted_value.
under eq_bigr do rewrite pushforward_coordinate mulr_suml.
rewrite exchange_big; apply eq_bigr => i _.
rewrite (bigD1 (f i)) // eqxx mulr1 /=.
have -> : \sum_(j | j != f i) (coordinate x i * (f i == j)%:R) * w j = 0.
  by apply big1 => j hj; rewrite eq_sym (negbTE hj) !mulr0 mul0r.
by rewrite addr0.
Qed.

Lemma weighted_continuous n (w : 'I_n.+1 -> Real) : continuous (@weighted_value n w).
Proof.
rewrite /weighted_value.
apply: continuous_big.
- move=> p; apply: continuousD; [exact: cvg_fst | exact: cvg_snd].
- move=> i _ x; apply: continuousM; [exact: coordinate_continuous | exact: cst_continuous].
Qed.

Lemma weighted_nonnegative n (w : 'I_n.+1 -> Real)
    (hw : forall i, 0 <= w i) (x : simplex Real n) : 0 <= weighted_value w x.
Proof.
apply sumr_ge0 => i _; apply mulr_ge0; [exact: coordinate_ge0 | exact: hw].
Qed.

Lemma weighted_le_one n (w : 'I_n.+1 -> Real)
    (hw : forall i, w i <= 1) (x : simplex Real n) : weighted_value w x <= 1.
Proof.
rewrite -(coordinate_sum x); apply ler_sum => i _.
apply: ler_piMr; [exact: coordinate_ge0 | exact: hw].
Qed.

Definition interval_weighted_value n (w : 'I_n.+1 -> Real)
    (h0 : forall i, 0 <= w i) (h1 : forall i, w i <= 1)
    (x : simplex Real n) : unit_interval Real.
Proof.
refine (exist _ (weighted_value w x) _); apply mem_set.
apply/andP; split; [exact: weighted_nonnegative | exact: weighted_le_one].
Defined.

Lemma interval_weighted_continuous n (w : 'I_n.+1 -> Real)
    (h0 : forall i, 0 <= w i) (h1 : forall i, w i <= 1) :
  continuous (@interval_weighted_value n w h0 h1).
Proof.
apply (@continuous_comp_initial _ _ _ set_val).
exact: weighted_continuous.
Qed.
End Scalar.
End DPTopologicalSimplexFunctions.
