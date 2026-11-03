From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  GeometricRealizationBoundaryAffine GeometricRealizationBoundaryFaces
  TopologicalSimplexBasic TopologicalSimplexAffine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPRealizationBoundarySupport.
Import DPSimplexCategory DPSimplexFactorization DPTopologicalSimplex
  DPTopologicalSimplexAffine DPRealizationBoundaryAffine DPRealizationBoundaryFaces.
Section Support.
Variable Real : realType.

Definition point_support n (x : simplex Real n) : {set 'I_n.+1} :=
  [set i | coordinate x i != 0].

Lemma point_support_positive n (x : simplex Real n) : (0 < #|point_support x|)%N.
Proof.
apply/card_gt0P.
case: (pselect (exists i, i \in point_support x)) => [h|h]; first exact h.
have hs : \sum_i coordinate x i = (0 : Real).
  apply: big1 => i _.
  case: (eqVneq (coordinate x i) 0) => [e|e]; first exact e.
  exfalso; apply: h; exists i; by rewrite /point_support inE.
have h10 : (1 : Real) = 0 by rewrite -(coordinate_sum x) hs.
by move/eqP: h10; rewrite oner_eq0.
Qed.

Lemma point_support_outside n (x : simplex Real n) i :
  i \notin point_support x -> coordinate x i = 0.
Proof. by rewrite /point_support inE negbK => /eqP. Qed.

Lemma boundary_support_proper n (x : simplex Real n) (hx : @boundary_set Real n x) :
  point_support x != finset.setT.
Proof.
apply/eqP => e. destruct hx as [i hi].
have hm : i \in point_support x by rewrite e finset.in_setT.
by move: hm; rewrite /point_support inE hi eqxx.
Qed.

Definition face_point n (A : {set 'I_n.+1}) (hA : (0 < #|A|)%N)
    (x : simplex Real n) : simplex Real (face_dimension A) :=
  pushforward (vertex_preimage (@face_inclusion n A hA)) x.

Lemma face_point_evaluation n (A : {set 'I_n.+1}) (hA : (0 < #|A|)%N)
    (x : simplex Real n) (hx : forall i, i \notin A -> coordinate x i = 0) :
  pushforward (@face_inclusion n A hA) (face_point hA x) = x.
Proof.
apply: pushforward_preimage_supported => j hj.
apply: hx; apply/negP => hmem.
have [i hi] := proj2 (@face_inclusion_image n A hA j) hmem.
exact: (hj i hi).
Qed.

Definition support_inclusion n (x : simplex Real n) :
    ordinal_map (face_dimension (point_support x)) n :=
  @face_inclusion n (point_support x) (point_support_positive x).

Definition support_point n (x : simplex Real n) :
    simplex Real (face_dimension (point_support x)) :=
  face_point (point_support_positive x) x.

Lemma support_point_evaluation n (x : simplex Real n) :
  pushforward (support_inclusion x) (support_point x) = x.
Proof. apply: face_point_evaluation; exact: point_support_outside. Qed.

Lemma support_inclusion_nonsurjective n (x : simplex Real n) (hx : @boundary_set Real n x) :
  ~ ordinal_surjective (support_inclusion x).
Proof. apply: face_inclusion_nonsurjective. exact: boundary_support_proper. Qed.

Lemma nonsurjective_missing_vertex n m (f : ordinal_map n m)
    (hf : ~ ordinal_surjective f) : exists j, forall i, f i <> j.
Proof.
have hall : ~~ [forall j, j \in codom f].
  apply/negP => /forallP h; apply: hf => j.
  have [i hi] := (elimT codomP (h j)). exists i; symmetry; exact hi.
move/forallPn: hall => [j hj]. exists j => i hi.
have hm : j \in codom f by apply/codomP; exists i; symmetry; exact hi.
by move: hj; rewrite hm.
Qed.

Lemma nonsurjective_pushforward_boundary n m (f : ordinal_map n m)
    (hf : ~ ordinal_surjective f) (x : simplex Real n) :
  @boundary_set Real m (pushforward f x).
Proof.
have [j hj] := nonsurjective_missing_vertex hf. exists j.
exact: pushforward_missing_coordinate.
Qed.

End Support.
End DPRealizationBoundarySupport.
