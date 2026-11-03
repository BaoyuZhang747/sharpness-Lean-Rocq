(** Actual affine pullback of singular simplices and signed subdivision operators. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplicialSet SimplicialChains SimplicialChainsMaps
  SingularSet TopologicalCategory TopologicalSimplexBasic
  SingularSubdivisionGeometryAffine SingularSubdivisionGeometryBarycenter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPTopological DPSingularSet
  DPSingularSubdivisionAffine DPSingularSubdivisionBarycenter
  DPSimplicialChains DPSimplicialChainMaps.
Local Open Scope ring_scope.

Module DPSingularSubdivision.
Section Simplices.
Variable Real : realType.
Variable X : topologicalType.

Definition singular_affine_pull {n m}
    (v : 'I_m.+1 -> DPTopologicalSimplex.simplex Real n)
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
    DPSimplicialSet.simplex (singular_set Real X) m :=
  continuous_compose (affine_simplex_map v) s.

Lemma singular_affine_pull_at {n m}
    (v : 'I_m.+1 -> DPTopologicalSimplex.simplex Real n)
    (s : DPSimplicialSet.simplex (singular_set Real X) n) x :
  singular_affine_pull v s x = s (affine_simplex v x).
Proof. reflexivity. Qed.

Definition singular_barycentric_cell n (p : {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
    DPSimplicialSet.simplex (singular_set Real X) n :=
  singular_affine_pull (prefix_barycenter Real p) s.

Lemma singular_barycentric_cell_at n (p : {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex (singular_set Real X) n) x :
  singular_barycentric_cell p s x = s (barycentric_cell Real p x).
Proof. reflexivity. Qed.

Lemma singular_barycentric_cell_in_set n (p : {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex (singular_set Real X) n) (U : X -> Prop) :
  (forall x, U (s x)) -> forall x, U (singular_barycentric_cell p s x).
Proof. move=> h x; exact: h. Qed.

Lemma singular_barycentric_cell_zero (p : {perm 'I_1})
    (s : DPSimplicialSet.simplex (singular_set Real X) 0) :
  singular_barycentric_cell p s = s.
Proof.
apply topological_hom_ext => x; rewrite singular_barycentric_cell_at barycentric_cell_zero.
reflexivity.
Qed.

End Simplices.

Lemma singular_barycentric_cell_naturality (Real : realType) (X Y : topologicalType)
    (f : hom topological_category X Y) n (p : {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  component (singular_map Real f) n (singular_barycentric_cell p s) =
    singular_barycentric_cell p (component (singular_map Real f) n s).
Proof. apply topological_hom_ext => x; reflexivity. Qed.

Section Chains.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.

Definition subdivision_at n (a : term R (singular_set Real X) n) :
    term R (singular_set Real X) n :=
  \sum_(p : {perm 'I_n.+1}) (-1 : R)^+(odd_perm p) *:
    free_map R (singular_barycentric_cell p) a.
Arguments subdivision_at n a : clear implicits.

Lemma subdivision_at_linear n : linear (subdivision_at n).
Proof.
move=> r a b; rewrite /subdivision_at scaler_sumr -big_split.
apply eq_bigr => p _; by rewrite linearP scalerDr !scalerA commr_sign.
Qed.
Arguments subdivision_at_linear n : clear implicits.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (subdivision_at n) (subdivision_at_linear n).

Lemma subdivision_at_basis n (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  subdivision_at n (free_basis R s) =
    \sum_(p : {perm 'I_n.+1}) (-1 : R)^+(odd_perm p) *:
      free_basis R (singular_barycentric_cell p s).
Proof. apply eq_bigr => p _; by rewrite free_map_basis. Qed.

End Chains.
Arguments subdivision_at Real R X n a : clear implicits.

Lemma subdivision_naturality (Real : realType) (R : pzRingType)
    (X Y : topologicalType) (f : hom topological_category X Y) n
    (a : term R (singular_set Real X) n) :
  map_at R (singular_map Real f) n (subdivision_at Real R X n a) =
    subdivision_at Real R Y n (map_at R (singular_map Real f) n a).
Proof.
rewrite /subdivision_at linear_sum; apply eq_bigr => p _; rewrite linearZ.
congr (_ *: _).
apply (free_lift_ext
  (g := (map_at R (singular_map Real f) n \o
    free_map R (@singular_barycentric_cell Real X n p) : {linear _ -> _}))
  (h := (free_map R (@singular_barycentric_cell Real Y n p) \o
    map_at R (singular_map Real f) n : {linear _ -> _}))).
move=> s; change (map_at R (singular_map Real f) n
  (free_map R (@singular_barycentric_cell Real X n p) (free_basis R s)) =
  free_map R (@singular_barycentric_cell Real Y n p)
    (map_at R (singular_map Real f) n (free_basis R s))).
by rewrite /map_at !free_map_basis singular_barycentric_cell_naturality.
Qed.

Lemma subdivision_degree_zero (Real : realType) (R : pzRingType)
    (X : topologicalType) (a : term R (singular_set Real X) 0) :
  subdivision_at Real R X 0 a = a.
Proof.
have hperm (p : {perm 'I_1}) : p = 1%g.
  apply/permP => i; by rewrite (ord1 (p i)) (ord1 ((1%g : {perm 'I_1}) i)).
rewrite /subdivision_at (bigD1 (1%g : {perm 'I_1})) //.
have hz : \sum_(p : {perm 'I_1} | p != 1%g) (-1 : R)^+(odd_perm p) *:
    free_map R (@singular_barycentric_cell Real X 0 p) a = 0.
  apply big1 => p hp; by rewrite (hperm p) eqxx in hp.
rewrite hz.
change (((-1 : R)^+(odd_perm (1%g : {perm 'I_1})) *:
  free_map R (@singular_barycentric_cell Real X 0 (1%g : {perm 'I_1})) a) + 0 = a).
rewrite addr0 odd_perm1 expr0 scale1r.
apply (free_lift_ext
  (g := free_map R (@singular_barycentric_cell Real X 0 (1%g : {perm 'I_1})))
  (h := (idfun : {linear term R (singular_set Real X) 0 -> term R (singular_set Real X) 0}))).
move=> s; by rewrite free_map_basis singular_barycentric_cell_zero.
Qed.

End DPSingularSubdivision.

