(** Actual continuity of radial projection on the punctured simplex subspace. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic
  TopologicalSimplexContinuity SingularSubdivisionGeometryBarycenter SingularSimplexRadialCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopological DPTopologicalSimplex DPTopologicalSimplexContinuity
  DPSingularSubdivisionBarycenter DPSingularSimplexRadialCoordinates.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularSimplexRadialContinuity.
Section Continuity.
Variable Real : realType.

Lemma coordinate_minimum_continuous n : continuous (@coordinate_minimum Real n).
Proof.
apply: continuous_big.
- move=> p; apply: continuous_min; [exact: cvg_fst | exact: cvg_snd].
- move=> i _; exact: coordinate_continuous.
Qed.

Lemma radial_gap_continuous n : continuous (@radial_gap Real n).
Proof.
rewrite /radial_gap; move=> x.
apply: (@continuousB Real _ (simplex_space Real n)
  (fun _ => (1 : Real)) (fun y => n.+1%:R * coordinate_minimum y) x);
  first exact: cst_continuous.
apply: continuousM; [exact: cst_continuous | exact: coordinate_minimum_continuous].
Qed.

Definition punctured_set n : set (simplex Real n) := [set x | x <> uniform_simplex Real n].
Arguments punctured_set n : clear implicits.
Definition punctured n := set_type (punctured_set n).
Definition punctured_space n : topologicalType := [the topologicalType of punctured n].
Definition punctured_val {n} (x : punctured n) : simplex Real n := val x.

Lemma punctured_property {n} (x : punctured n) : punctured_val x <> uniform_simplex Real n.
Proof. exact (set_valP x). Qed.

Lemma punctured_val_continuous n : continuous (@punctured_val n).
Proof. exact: initial_continuous. Qed.

Lemma punctured_minimum_continuous n :
  continuous (fun x : punctured_space n => coordinate_minimum (punctured_val x)).
Proof.
move=> x; apply: (@continuous_comp (punctured_space n) (simplex_space Real n) Real
  (@punctured_val n) (@coordinate_minimum Real n) x);
  [exact: punctured_val_continuous | exact: coordinate_minimum_continuous].
Qed.

Lemma punctured_gap_continuous n :
  continuous (fun x : punctured_space n => radial_gap (punctured_val x)).
Proof.
move=> x; apply: (@continuous_comp (punctured_space n) (simplex_space Real n) Real
  (@punctured_val n) (@radial_gap Real n) x);
  [exact: punctured_val_continuous | exact: radial_gap_continuous].
Qed.

Lemma punctured_coordinate_continuous n i :
  continuous (fun x : punctured_space n => coordinate (punctured_val x) i).
Proof.
move=> x; apply: (@continuous_comp (punctured_space n) (simplex_space Real n) Real
  (@punctured_val n) (@coordinate Real n ^~ i) x);
  [exact: punctured_val_continuous | exact: coordinate_continuous].
Qed.

Definition punctured_radial_vector {n} (x : punctured n) := radial_vector (punctured_val x).

Lemma punctured_radial_vector_continuous n : continuous (@punctured_radial_vector n).
Proof.
apply: (@matrix_continuous_from_coordinates (punctured_space n) Real 1 n.+1
  (@punctured_radial_vector n)) => i j x.
have ei : i = ord0 := ord1 i; subst i.
have ef : (fun y : punctured_space n => punctured_radial_vector y ord0 j) =
  (fun y : punctured_space n =>
  (coordinate (punctured_val y) j - coordinate_minimum (punctured_val y)) *
    (radial_gap (punctured_val y))^-1).
  apply funext => y; by rewrite /punctured_radial_vector /radial_vector mxE.
rewrite ef.
apply: (@continuousM Real (punctured_space n) _ _ x).
- apply: (@continuousB Real _ (punctured_space n) _ _ x);
    [exact: punctured_coordinate_continuous | exact: punctured_minimum_continuous].
- apply: (@continuousV Real (punctured_space n) _ x); last exact: punctured_gap_continuous.
  apply/eqP => e; have hp := radial_gap_pos (@punctured_property n x); by rewrite e ltxx in hp.
Qed.

Definition punctured_radial_point {n} (x : punctured n) : simplex Real n :=
  radial_projection (@punctured_property n x).

Lemma punctured_radial_point_continuous n : continuous (@punctured_radial_point n).
Proof.
apply: (@continuous_comp_initial _ (punctured_space n) _ set_val).
exact: punctured_radial_vector_continuous.
Qed.

Definition punctured_radial_boundary {n} (x : punctured n) : boundary Real n :=
  exist _ (punctured_radial_point x) (mem_set (radial_projection_boundary (@punctured_property n x))).

Lemma punctured_radial_boundary_continuous n : continuous (@punctured_radial_boundary n).
Proof.
apply: (@continuous_comp_initial _ (punctured_space n) _ set_val).
exact: punctured_radial_point_continuous.
Qed.

Definition radial_boundary_map n : continuousType (punctured_space n) (boundary_space Real n) :=
  continuous_map (@punctured_radial_boundary_continuous n).

Definition boundary_to_punctured {n} (b : boundary Real n) : punctured n :=
  exist _ (val b) (mem_set (boundary_not_uniform (set_valP b))).

Lemma boundary_to_punctured_continuous n : continuous (@boundary_to_punctured n).
Proof.
apply: (@continuous_comp_initial _ (boundary_space Real n) _ set_val).
exact: initial_continuous.
Qed.

Definition boundary_punctured_map n : continuousType (boundary_space Real n) (punctured_space n) :=
  continuous_map (@boundary_to_punctured_continuous n).

Theorem radial_boundary_map_retraction n (b : boundary Real n) :
  radial_boundary_map n (boundary_punctured_map n b) = b.
Proof.
apply val_inj; change (radial_projection (@punctured_property n (boundary_to_punctured b)) = val b).
apply radial_projection_fixes_boundary; exact: set_valP.
Qed.

End Continuity.
End DPSingularSimplexRadialContinuity.





