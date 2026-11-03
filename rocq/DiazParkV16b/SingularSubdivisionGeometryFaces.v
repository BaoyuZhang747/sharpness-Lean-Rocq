(** Geometric face comparisons of the actual barycentric cells. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  TopologicalSimplexBasic TopologicalSimplexAffine
  SingularSubdivisionGeometryAffine SingularSubdivisionGeometryBarycenter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopologicalSimplex DPTopologicalSimplexAffine DPSingularSubdivisionAffine
  DPSingularSubdivisionBarycenter DPSimplexCategory DPSimplexOperators DPSimplexIdentities.

Module DPSingularSubdivisionFaces.
Section Faces.
Variable Real : realType.

Lemma affine_simplex_ext_vertices {n m} (v w : 'I_n.+1 -> simplex Real m)
    (h : forall i, v i = w i) (x : simplex Real n) : affine_simplex v x = affine_simplex w x.
Proof. have e : v = w by apply functional_extensionality_dep. by rewrite e. Qed.

Lemma barycenter_ext {n m} (v w : 'I_n.+1 -> simplex Real m)
    (h : forall i, v i = w i) : barycenter v = barycenter w.
Proof. have e : v = w by apply functional_extensionality_dep. by rewrite e. Qed.

Lemma pushforward_affine {n m k} (f : 'I_m.+1 -> 'I_k.+1)
    (v : 'I_n.+1 -> simplex Real m) (x : simplex Real n) :
  pushforward f (affine_simplex v x) = affine_simplex (fun i => pushforward f (v i)) x.
Proof.
rewrite -(affine_simplex_pushforward f (affine_simplex v x)) affine_simplex_composition.
apply affine_simplex_ext_vertices => i; exact: affine_simplex_pushforward.
Qed.

Lemma pushforward_barycenter {n m k} (f : 'I_m.+1 -> 'I_k.+1)
    (v : 'I_n.+1 -> simplex Real m) :
  pushforward f (barycenter v) = barycenter (fun i => pushforward f (v i)).
Proof. exact: pushforward_affine. Qed.

Lemma prefix_barycenter_initial_segment n (p : {perm 'I_n.+2}) (q : {perm 'I_n.+1})
    (c : 'I_n.+2) (hp : forall j : 'I_n.+1, p (vertex_widen j) = coface c (q j))
    (k : 'I_n.+1) :
  prefix_barycenter Real p (vertex_widen k) =
    pushforward (coface c) (prefix_barycenter Real q k).
Proof.
rewrite /prefix_barycenter pushforward_barycenter.
apply barycenter_ext => i; rewrite pushforward_vertex.
have e : widen_ord (ltn_ord (vertex_widen k)) i =
    vertex_widen (widen_ord (ltn_ord k) i).
  by apply val_inj.
by rewrite e hp.
Qed.

Lemma coface_last_widen n (k : 'I_n.+1) :
  coface (ord_max : 'I_n.+2) k = vertex_widen k.
Proof.
apply val_inj; change (coface_value n.+1 k = val k).
unfold coface_value.
have h : PeanoNat.Nat.leb n.+1 k = false.
  apply PeanoNat.Nat.leb_gt; exact (elimT ssrnat.ltP (ltn_ord k)).
by rewrite h.
Qed.

Lemma barycentric_cell_outer_face n (p : {perm 'I_n.+2}) (q : {perm 'I_n.+1})
    (c : 'I_n.+2) (hp : forall j : 'I_n.+1, p (vertex_widen j) = coface c (q j))
    (x : simplex Real n) :
  barycentric_cell Real p (pushforward (coface ord_max) x) =
    pushforward (coface c) (barycentric_cell Real q x).
Proof.
change (affine_simplex (prefix_barycenter Real p) (pushforward (coface ord_max) x) =
  pushforward (coface c) (affine_simplex (prefix_barycenter Real q) x)).
rewrite affine_simplex_precompose pushforward_affine.
apply affine_simplex_ext_vertices => i.
rewrite /comp coface_last_widen.
exact (@prefix_barycenter_initial_segment n p q c hp i).
Qed.

End Faces.
End DPSingularSubdivisionFaces.
