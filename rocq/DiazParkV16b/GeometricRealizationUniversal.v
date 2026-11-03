From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology matrix_normedtype subtype_topology
  sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet TopologicalCategory
  TopologicalSimplexBasic TopologicalSimplexAffine GeometricRealizationCarrier.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope quotient_scope.
Local Open Scope classical_set_scope.

Module DPGeometricRealizationUniversal.
Import DPSimplexCategory DPTopological DPGeometricRealization.
Section Universal.
Variable Real : realType.
Variable X : DPSimplicialSet.simplicial_set.
Variable Y : topologicalType.

Definition simplex_family := forall n, DPSimplicialSet.simplex X n ->
  DPTopologicalSimplex.simplex Real n -> Y.

Definition family_compatible (f : simplex_family) :=
  forall n m (a : ordinal_map n m) (x : DPSimplicialSet.simplex X m)
    (t : DPTopologicalSimplex.simplex Real n),
  f n (DPSimplicialSet.simplex_map X a x) t =
    f m x (DPTopologicalSimplexAffine.pushforward a t).

Definition raw_evaluate (f : simplex_family) (p : pre_realization Real X) : Y :=
  match p with @existT _ _ (@existT _ _ n x) t => f n x t end.

Lemma raw_evaluate_at (f : simplex_family) n (x : DPSimplicialSet.simplex X n) t :
  raw_evaluate f (@pre_point Real X n x t) = f n x t.
Proof. reflexivity. Qed.

Lemma raw_evaluate_equivalent (f : simplex_family) (hf : family_compatible f)
    p q : realization_equivalent p q -> raw_evaluate f p = raw_evaluate f q.
Proof.
move=> h; elim: h => [p0|p0 q0 hpq ih|p0 q0 r0 hpq ih hqr ih'|n m a x t].
- reflexivity.
- exact: esym ih.
- exact: etrans ih ih'.
- exact: hf.
Qed.

Lemma raw_evaluate_continuous (f : simplex_family) :
  (forall n x, continuous (f n x)) -> continuous (raw_evaluate f).
Proof.
move=> hf [[n x] t] U hU.
exact: (hf n x t U hU).
Qed.

Definition descent (f : simplex_family) (z : realization Real X) : Y :=
  raw_evaluate f (repr z).

Lemma descent_class (f : simplex_family) (hf : family_compatible f)
    (p : pre_realization Real X) : descent f (realization_class p) = raw_evaluate f p.
Proof.
rewrite /descent.
apply: (@raw_evaluate_equivalent f hf (repr (realization_class p)) p).
apply/realization_class_eq; exact: reprK.
Qed.

Lemma descent_characteristic (f : simplex_family) (hf : family_compatible f)
    n (x : DPSimplicialSet.simplex X n) t :
  descent f (@characteristic Real X n x t) = f n x t.
Proof. exact: descent_class. Qed.

Lemma descent_continuous (f : simplex_family) (hf : family_compatible f)
    (hc : forall n x, continuous (f n x)) : continuous (descent f).
Proof.
apply/quotient_continuous.
have he : (descent f \o @realization_class Real X) = raw_evaluate f.
  apply: funext => p; exact: descent_class.
rewrite he; exact: raw_evaluate_continuous.
Qed.

Lemma characteristic_ext (f g : realization Real X -> Y) :
  (forall n (x : DPSimplicialSet.simplex X n) t,
    f (@characteristic Real X n x t) = g (@characteristic Real X n x t)) -> f = g.
Proof.
move=> h; apply: funext => z.
have [[[n x] t] <-] := realization_class_surjective z.
exact: h.
Qed.

Definition descent_map (f : simplex_family) (hf : family_compatible f)
    (hc : forall n x, continuous (f n x)) :
    hom topological_category (realization_space Real X) Y :=
  continuous_map (@descent_continuous f hf hc).

Lemma descent_map_unique (f : simplex_family) (hf : family_compatible f)
    (hc : forall n x, continuous (f n x))
    (g : hom topological_category (realization_space Real X) Y) :
  (forall n (x : DPSimplicialSet.simplex X n) t,
    g (@characteristic Real X n x t) = f n x t) -> g = descent_map hf hc.
Proof.
move=> h; apply: topological_hom_ext => z.
have [[[n x] t] <-] := realization_class_surjective z.
rewrite h; symmetry; exact: descent_characteristic.
Qed.

End Universal.
End DPGeometricRealizationUniversal.
