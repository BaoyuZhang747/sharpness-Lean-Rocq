From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryCompact
  TopologicalSimplexBasic TopologicalSimplexAffine TopologicalSimplexContinuity
  TopologicalSimplexCompact.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalSimplexFaces.
Import DPTopological DPTopologicalCompact DPTopologicalSimplex
  DPTopologicalSimplexAffine DPTopologicalSimplexContinuity DPTopologicalSimplexCompact.
Section Faces.
Variable Real : realType.

Lemma injective_pushforward_coordinate {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (hf : injective f) (x : simplex Real n) i :
  coordinate (pushforward f x) (f i) = coordinate x i.
Proof.
rewrite pushforward_coordinate (bigD1 i) // eqxx /= mulr1.
have -> : \sum_(j | j != i) coordinate x j * (f j == f i)%:R = (0 : Real).
  apply: big1 => j hj.
  have hfj : f j != f i by apply/negP => /eqP /hf /eqP; exact: negP hj.
  by rewrite (negbTE hfj) mulr0.
by rewrite addr0.
Qed.

Lemma pushforward_injective {n m} (f : 'I_n.+1 -> 'I_m.+1) :
  injective f -> injective (@pushforward Real n m f).
Proof.
move=> hf x y h; apply: simplex_ext => i.
have := congr1 (fun z => coordinate z (f i)) h.
by rewrite !injective_pushforward_coordinate.
Qed.

Lemma pushforward_coordinate_outside {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real n) j :
  (forall i, f i != j) -> coordinate (pushforward f x) j = 0.
Proof.
move=> h; rewrite pushforward_coordinate; apply: big1 => i _.
by rewrite (negbTE (h i)) mulr0.
Qed.

Lemma pushforward_into_boundary {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (j : 'I_m.+1) (h : forall i, f i != j) (x : simplex Real n) :
  @boundary_set Real m (pushforward f x).
Proof. exists j; exact: pushforward_coordinate_outside. Qed.

Lemma boundary_set_closed n : closed (@boundary_set Real n).
Proof.
have he : @boundary_set Real n =
    \bigcup_i [set x : simplex Real n | coordinate x i = 0].
  apply/seteqP; split=> x.
  - by move=> [i hi]; exists i.
  - by move=> [i _ hi]; exists i.
rewrite he; apply: closed_bigcup; first exact: finite_finset.
move=> i _; apply: (@preimage_closed _ _ (@coordinate Real n ^~ i) [set t | t = 0]);
  last exact: closed_eq.
by move=> x _; exact: coordinate_continuous.
Qed.

Lemma boundary_set_compact n : compact (@boundary_set Real n).
Proof.
apply: (@subclosed_compact _ _ setT (@boundary_set_closed n) (@simplex_compact Real n)).
by move=> x _.
Qed.

Lemma boundary_compact n : @compact (boundary_space Real n) setT.
Proof. apply: compact_subtype; exact: boundary_set_compact. Qed.

Definition simplex_zero_homeomorphism :
    homeomorphism (simplex_space Real 0) point_space.
Proof.
refine (@homeomorphism_of_inverse (simplex_space Real 0) point_space (fun _ => tt)
  (fun _ => @vertex Real 0 ord0) _ _ _ _).
- exact: cst_continuous.
- exact: cst_continuous.
- move=> x; exact: simplex_zero_unique.
- by case.
Defined.

End Faces.
End DPTopologicalSimplexFaces.
