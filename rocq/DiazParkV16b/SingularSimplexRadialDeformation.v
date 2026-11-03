(** Genuine continuous boundary-fixed deformation on the punctured simplex. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic TopologicalSimplexContinuity TopologicalSimplexContraction
  SingularSimplexRadialCoordinates SingularSimplexRadialContinuity
  SingularSimplexRadialDeformationGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports
  DPTopological DPTopologicalHomotopy DPTopologicalSimplex DPTopologicalSimplexContinuity
  DPTopologicalSimplexContraction DPSingularSimplexRadialCoordinates
  DPSingularSimplexRadialContinuity DPSingularSimplexRadialDeformationGeometry.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularSimplexRadialDeformation.
Section Deformation.
Variable Real : realType.

Lemma mix_maps_continuous (T : topologicalType) n (t : T -> unit_interval Real)
    (x y : T -> simplex Real n) (ht : continuous t) (hx : continuous x) (hy : continuous y) :
  continuous (fun z => mix (t z) (x z) (y z)).
Proof.
apply: (@continuous_comp_initial _ T _ set_val).
apply: (@matrix_continuous_from_coordinates T Real 1 n.+1
  (fun z => simplex_vector (mix (t z) (x z) (y z)))) => i j z.
have ei : i = ord0 := ord1 i; subst i.
have e : (fun w => simplex_vector (mix (t w) (x w) (y w)) ord0 j) =
  (fun w => (1 - val (t w)) * coordinate (x w) j + val (t w) * coordinate (y w) j).
  apply funext => w; exact: coordinate_mix.
rewrite e.
have ht' : continuous (fun w => val (t w)).
  move=> w; apply: (@continuous_comp T (unit_interval_space Real) Real t set_val w);
    [exact: ht | exact: interval_val_continuous].
have hx' : continuous (fun w => coordinate (x w) j).
  move=> w; apply: (@continuous_comp T (simplex_space Real n) Real x (@coordinate Real n ^~ j) w);
    [exact: hx | exact: coordinate_continuous].
have hy' : continuous (fun w => coordinate (y w) j).
  move=> w; apply: (@continuous_comp T (simplex_space Real n) Real y (@coordinate Real n ^~ j) w);
    [exact: hy | exact: coordinate_continuous].
apply: (@continuousD Real _ T _ _ z).
- apply: (@continuousM Real T _ _ z).
  + apply: (@continuousB Real _ T _ _ z); [exact: cst_continuous | exact: ht'].
  + exact: hx'.
- apply: (@continuousM Real T _ _ z); [exact: ht' | exact: hy'].
Qed.

Lemma radial_mix_continuous n :
  continuous (fun p : (unit_interval_space Real * punctured_space Real n)%type => radial_mix p.1 p.2).
Proof.
apply: (@continuous_comp_initial _
  [the topologicalType of (unit_interval_space Real * punctured_space Real n)%type] _ set_val).
change (continuous (fun p : (unit_interval_space Real * punctured_space Real n)%type =>
  mix p.1 (punctured_val p.2) (punctured_radial_point p.2))).
apply: mix_maps_continuous.
- move=> p; exact: cvg_fst.
- move=> p; apply: (@continuous_comp _ (punctured_space Real n) (simplex_space Real n)
    snd (@punctured_val Real n) p); [exact: cvg_snd | exact: punctured_val_continuous].
- move=> p; apply: (@continuous_comp _ (punctured_space Real n) (simplex_space Real n)
    snd (@punctured_radial_point Real n) p); [exact: cvg_snd | exact: punctured_radial_point_continuous].
Qed.

Definition radial_deformation n : continuous_homotopy Real
    (continuous_identity (punctured_space Real n))
    (continuous_compose (radial_boundary_map Real n) (boundary_punctured_map Real n)).
Proof.
refine (@ContinuousHomotopy Real _ _ _ _ (continuous_map (@radial_mix_continuous n)) _ _).
- exact: radial_mix_start.
- exact: radial_mix_end.
Defined.

Theorem radial_deformation_fixed n (t : unit_interval Real) (b : boundary Real n) :
  homotopy_map (radial_deformation n) (t, boundary_punctured_map Real n b) =
    boundary_punctured_map Real n b.
Proof. exact: radial_mix_fixed. Qed.

Theorem radial_deformation_at n (t : unit_interval Real) (x : punctured Real n) :
  punctured_val (homotopy_map (radial_deformation n) (t, x)) =
    mix t (punctured_val x) (radial_projection (@punctured_property Real n x)).
Proof. reflexivity. Qed.

End Deformation.
End DPSingularSimplexRadialDeformation.

