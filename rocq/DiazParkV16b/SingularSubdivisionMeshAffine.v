(** Coordinate sup-norm estimates for actual affine simplex maps.
    The finite vertex mesh is the maximum of the genuine pairwise distances. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalSimplexBasic TopologicalSimplexFunctions
  SingularSubdivisionGeometryAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory numFieldNormedType.Exports.
Import DPTopologicalSimplex DPTopologicalSimplexFunctions DPSingularSubdivisionAffine.
Local Open Scope ring_scope.

Module DPSingularSubdivisionMeshAffine.
Section Estimates.
Variable Real : realType.

Lemma weighted_sum_norm_bound (I : finType) (P : pred I)
    (a b : I -> Real) D (ha : forall i, P i -> 0 <= a i)
    (hb : forall i, P i -> `|b i| <= D) :
  `|\sum_(i | P i) a i * b i| <= (\sum_(i | P i) a i) * D.
Proof.
apply: (le_trans (ler_norm_sum _ _ _)).
rewrite mulr_suml; apply ler_sum => i hi.
rewrite normrM (ger0_norm (ha i hi)).
exact (ler_wpM2l (ha i hi) (hb i hi)).
Qed.

Lemma weighted_sub_const n (f : 'I_n.+1 -> Real) (x : simplex Real n) c :
  weighted_value f x - c = \sum_i coordinate x i * (f i - c).
Proof.
under eq_bigr do rewrite mulrBr.
by rewrite sumrB -mulr_suml coordinate_sum mul1r.
Qed.

Lemma weighted_sub_const_bound n (f : 'I_n.+1 -> Real) (x : simplex Real n) c D
    (h : forall i, `|f i - c| <= D) :
  `|weighted_value f x - c| <= D.
Proof.
rewrite weighted_sub_const.
have hsum := @weighted_sum_norm_bound [the finType of 'I_n.+1] predT
  (coordinate x) (fun i => f i - c) D (fun i _ => coordinate_ge0 x i) (fun i _ => h i).
by rewrite coordinate_sum mul1r in hsum.
Qed.

Lemma weighted_pairwise_bound n (f : 'I_n.+1 -> Real) (x y : simplex Real n) D
    (h : forall i j, `|f i - f j| <= D) :
  `|weighted_value f x - weighted_value f y| <= D.
Proof.
apply: weighted_sub_const_bound => i.
rewrite -opprB normrN; apply: weighted_sub_const_bound => j.
exact: h.
Qed.

Definition simplex_distance n (x y : simplex Real n) : Real :=
  `|simplex_vector x - simplex_vector y|.

Lemma simplex_distance_nonnegative n (x y : simplex Real n) :
  0 <= simplex_distance x y.
Proof. exact: normr_ge0. Qed.

Lemma simplex_distance_self n (x : simplex Real n) : simplex_distance x x = 0.
Proof. by rewrite /simplex_distance subrr normr0. Qed.

Lemma simplex_distance_symmetric n (x y : simplex Real n) :
  simplex_distance x y = simplex_distance y x.
Proof. by rewrite /simplex_distance -[simplex_vector x - _]opprB normrN. Qed.

Lemma simplex_coordinate_distance_le n (x y : simplex Real n) j :
  `|coordinate x j - coordinate y j| <= simplex_distance x y.
Proof.
have he : (simplex_vector x - simplex_vector y) ord0 j = coordinate x j - coordinate y j.
  by rewrite /coordinate !mxE.
rewrite -he.
change (`|(simplex_vector x - simplex_vector y) ord0 j| <=
  mx_norm (simplex_vector x - simplex_vector y)).
rewrite mx_normrE; apply/bigmax_geP; right.
by exists (ord0,j).
Qed.

Lemma simplex_distance_le n (x y : simplex Real n) D (hD : 0 <= D)
    (h : forall j, `|coordinate x j - coordinate y j| <= D) :
  simplex_distance x y <= D.
Proof.
change (mx_norm (simplex_vector x - simplex_vector y) <= D).
rewrite mx_normrE; apply/bigmax_leP; split=> // -[i j] _.
rewrite (ord1 i) !mxE; exact: h.
Qed.

Lemma affine_simplex_distance_bound n m (v : 'I_n.+1 -> simplex Real m) D
    (hD : 0 <= D) (h : forall i j, simplex_distance (v i) (v j) <= D)
    (x y : simplex Real n) :
  simplex_distance (affine_simplex v x) (affine_simplex v y) <= D.
Proof.
apply: (simplex_distance_le hD) => j; rewrite !affine_simplex_coordinate.
change (`|weighted_value (fun i => coordinate (v i) j) x -
  weighted_value (fun i => coordinate (v i) j) y| <= D).
apply: weighted_pairwise_bound => a b.
exact (le_trans (simplex_coordinate_distance_le (v a) (v b) j) (h a b)).
Qed.

Definition vertex_mesh n m (v : 'I_n.+1 -> simplex Real m) : Real :=
  \big[maxr/0]_(ij : 'I_n.+1 * 'I_n.+1) simplex_distance (v ij.1) (v ij.2).

Lemma vertex_mesh_nonnegative n m (v : 'I_n.+1 -> simplex Real m) :
  0 <= vertex_mesh v.
Proof. exact: bigmax_ge_id. Qed.

Lemma vertex_distance_le_mesh n m (v : 'I_n.+1 -> simplex Real m) i j :
  simplex_distance (v i) (v j) <= vertex_mesh v.
Proof. apply/bigmax_geP; right; by exists (i,j). Qed.

Lemma vertex_mesh_le n m (v : 'I_n.+1 -> simplex Real m) D
    (hD : 0 <= D) (h : forall i j, simplex_distance (v i) (v j) <= D) :
  vertex_mesh v <= D.
Proof. apply/bigmax_leP; split=> // -[i j] _; exact: h. Qed.

Lemma affine_simplex_distance_le_mesh n m (v : 'I_n.+1 -> simplex Real m)
    (x y : simplex Real n) :
  simplex_distance (affine_simplex v x) (affine_simplex v y) <= vertex_mesh v.
Proof. exact: (affine_simplex_distance_bound (vertex_mesh_nonnegative v) (vertex_distance_le_mesh v)). Qed.

Lemma vertex_mesh_zero_dimension m (v : 'I_1 -> simplex Real m) : vertex_mesh v = 0.
Proof.
apply/eqP; rewrite eq_le vertex_mesh_nonnegative andbT.
apply: vertex_mesh_le => // i j.
by rewrite (ord1 i) (ord1 j) simplex_distance_self.
Qed.

End Estimates.
End DPSingularSubdivisionMeshAffine.
