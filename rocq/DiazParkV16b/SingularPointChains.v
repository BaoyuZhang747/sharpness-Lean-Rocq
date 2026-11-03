(** Actual singular chains of a point and their positive exactness. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic
  SimplicialSet SingularSet SimplicialChains SingularCohomology
  ChainComplex AlternatingSign.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPTopological DPTopologicalSimplex
  DPSimplicialSet DPSingularSet DPSimplicialChains DPSingularCohomology
  DPChainComplex DPAlternatingSign.
Local Open Scope ring_scope.

Module DPSingularPointChains.
Section Point.
Variable Real : realType.
Variable R : pzRingType.
Let K := singular_chains Real R point_space.

Definition point_simplex n := point_map (simplex_space Real n).
Definition point_regrade n m : {linear chain_term K n -> chain_term K m} :=
  free_map R (fun _ => point_simplex m).

Lemma point_regrade_basis n m (s : simplex (singular_set Real point_space) n) :
  point_regrade n m (free_basis R s) = free_basis R (point_simplex m).
Proof. exact: free_map_basis. Qed.

Lemma point_regrade_cancel n m (x : chain_term K n) :
  point_regrade m n (point_regrade n m x) = x.
Proof.
apply: (free_lift_ext (g := (point_regrade m n \o point_regrade n m : {linear _ -> _}))
  (h := (idfun : {linear chain_term K n -> chain_term K n}))).
move=> s; rewrite /= !point_regrade_basis.
congr (free_basis R _); symmetry; exact: point_map_unique.
Qed.

Lemma point_face_regrade n i (x : chain_term K n.+1) :
  face_map R (singular_set Real point_space) n i x = point_regrade n.+1 n x.
Proof.
apply: (free_lift_ext (g := face_map R (singular_set Real point_space) n i)
  (h := point_regrade n.+1 n)).
move=> s; rewrite /face_map free_map_basis point_regrade_basis.
congr (free_basis R _); exact: point_map_unique.
Qed.

Lemma point_boundary n (x : chain_term K n.+1) :
  chain_d K n x = if odd n then point_regrade n.+1 n x else 0.
Proof.
change (@DPSimplicialChains.boundary R (singular_set Real point_space) n x =
  if odd n then point_regrade n.+1 n x else 0).
rewrite /DPSimplicialChains.boundary.
under eq_bigr do rewrite point_face_regrade.
rewrite -scaler_suml sum_sign !oddS negbK.
by case: (odd n); rewrite ?scale1r ?scale0r.
Qed.

Theorem point_positive_exact n (x : chain_term K n.+1) :
  @cycle R K n.+1 x -> @DPChainComplex.boundary R K n.+1 x.
Proof.
move=> hx; case hn : (odd n).
- have ex : point_regrade n.+1 n x = 0.
    change (chain_d K n x = 0) in hx; by rewrite point_boundary hn in hx.
  have ex0 : x = 0.
    rewrite -(point_regrade_cancel n x) ex linear0; reflexivity.
  exists 0; by rewrite ex0 linear0.
- exists (point_regrade n.+1 n.+2 x).
  by rewrite point_boundary oddS hn /= point_regrade_cancel.
Qed.
End Point.
End DPSingularPointChains.
