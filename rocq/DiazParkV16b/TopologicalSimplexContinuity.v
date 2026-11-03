From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexVectors
  TopologicalSimplexBasic TopologicalSimplexAffine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalSimplexContinuity.
Import DPTopological DPTopologicalSimplex DPTopologicalSimplexVectors
  DPTopologicalSimplexAffine.

Lemma matrix_continuous_from_coordinates {X Y : topologicalType} m n
    (f : X -> 'M[Y]_(m,n)) :
  (forall i j, continuous (fun x => f x i j)) -> continuous f.
Proof.
move=> hf x U [P hP hPU].
apply: (filterS hPU).
apply: filter_forall => i; apply: filter_forall => j.
exact: (hf i j x _ (hP i j)).
Qed.

Section Continuity.
Variable Real : realType.

Lemma simplex_vector_continuous n :
  continuous (@simplex_vector Real n).
Proof. exact: initial_continuous. Qed.

Lemma coordinate_continuous n i : continuous (@coordinate Real n ^~ i).
Proof.
move=> x; apply: (@continuous_comp _ _ _ (@simplex_vector Real n)
  (fun M : 'rV[Real]_n.+1 => M ord0 i) x); first exact: simplex_vector_continuous.
exact: coord_continuous.
Qed.

Lemma push_vector_continuous {n m} (f : 'I_n.+1 -> 'I_m.+1) :
  continuous (@push_vector Real n m f).
Proof.
apply: matrix_continuous_from_coordinates => i j.
have -> : i = ord0 := ord1 i.
have -> : (fun x : 'rV[Real]_n.+1 => push_vector f x ord0 j) =
    (fun x => \sum_k x ord0 k * (f k == j)%:R).
  by apply: funext => x; rewrite push_vector_coordinate.
apply: continuous_big.
- move=> p; apply: continuousD; [exact: cvg_fst | exact: cvg_snd].
move=> k _ x; apply: (@continuousM Real _
  (fun y : 'rV[Real]_n.+1 => y ord0 k) (fun _ => (f k == j)%:R) x);
  first exact: coord_continuous.
exact: cst_continuous.
Qed.

Lemma pushforward_continuous {n m} (f : 'I_n.+1 -> 'I_m.+1) :
  continuous (@pushforward Real n m f).
Proof.
apply: (@continuous_comp_initial _ _ _ set_val).
move=> x; apply: (@continuous_comp _ _ _ (@simplex_vector Real n)
  (@push_vector Real n m f) x); first exact: simplex_vector_continuous.
exact: push_vector_continuous.
Qed.

Definition simplex_map {n m} (f : 'I_n.+1 -> 'I_m.+1) :
    hom topological_category (simplex_space Real n) (simplex_space Real m) :=
  continuous_map (@pushforward_continuous n m f).

Lemma simplex_map_at {n m} (f : 'I_n.+1 -> 'I_m.+1) (x : simplex Real n) :
  simplex_map f x = pushforward f x.
Proof. reflexivity. Qed.

Lemma simplex_map_identity n :
  simplex_map (@idfun 'I_n.+1) = @identity topological_category (simplex_space Real n).
Proof. apply: topological_hom_ext => x; exact: pushforward_identity. Qed.

Lemma simplex_map_composition {n m k} (f : 'I_n.+1 -> 'I_m.+1)
    (g : 'I_m.+1 -> 'I_k.+1) :
  compose (simplex_map f) (simplex_map g) = simplex_map (g \o f).
Proof. apply: topological_hom_ext => x; exact: pushforward_composition. Qed.

End Continuity.
End DPTopologicalSimplexContinuity.
