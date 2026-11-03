(** The literal straight radial interpolation remains in the punctured simplex. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalCategoryHomotopy TopologicalSimplexBasic
  TopologicalSimplexContraction SingularSubdivisionGeometryBarycenter
  SingularSimplexRadialCoordinates SingularSimplexRadialContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports
  DPTopologicalHomotopy DPTopologicalSimplex DPTopologicalSimplexContraction
  DPSingularSubdivisionBarycenter DPSingularSimplexRadialCoordinates
  DPSingularSimplexRadialContinuity.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularSimplexRadialDeformationGeometry.
Section Geometry.
Variable Real : realType.

Lemma coordinate_minimum_lt_uniform n (x : simplex Real n)
    (hx : x <> uniform_simplex Real n) : coordinate_minimum x < (n.+1%:R : Real)^-1.
Proof.
have hp := radial_gap_pos hx.
rewrite /radial_gap subr_gt0 in hp.
have hn : (0 : Real) < n.+1%:R by rewrite ltr0n.
by rewrite -(mulr1 ((n.+1%:R : Real)^-1)) (ltr_pdivlMl _ _ hn).
Qed.

Lemma coordinate_mix n (t : unit_interval Real) (x y : simplex Real n) i :
  coordinate (mix t x y) i = (1 - val t) * coordinate x i + val t * coordinate y i.
Proof. exact: mix_vector_coordinate. Qed.

Lemma radial_mix_minimum_coordinate n (x : simplex Real n)
    (hx : x <> uniform_simplex Real n) (t : unit_interval Real) i
    (hi : coordinate_minimum x = coordinate x i) :
  coordinate (mix t x (radial_projection hx)) i = (1 - val t) * coordinate_minimum x.
Proof. by rewrite coordinate_mix radial_projection_coordinate -hi subrr mul0r mulr0 addr0. Qed.

Theorem radial_mix_not_uniform n (x : simplex Real n)
    (hx : x <> uniform_simplex Real n) (t : unit_interval Real) :
  mix t x (radial_projection hx) <> uniform_simplex Real n.
Proof.
have [i hi] := coordinate_minimum_attained x.
have hm : (1 - val t) * coordinate_minimum x <= coordinate_minimum x.
  rewrite mulrBl mul1r lerBlDr lerDl.
  exact: mulr_ge0 (interval_ge0 t) (coordinate_minimum_ge0 x).
have hlt := le_lt_trans hm (coordinate_minimum_lt_uniform hx).
move=> e; have he := congr1 (fun y => coordinate y i) e.
rewrite (radial_mix_minimum_coordinate hx t hi) uniform_simplex_coordinate in he.
by rewrite he ltxx in hlt.
Qed.

Definition radial_mix n (t : unit_interval Real) (x : punctured Real n) : punctured Real n :=
  exist _ (mix t (punctured_val x) (punctured_radial_point x))
    (mem_set (@radial_mix_not_uniform n (punctured_val x) (@punctured_property Real n x) t)).

Lemma radial_mix_val n (t : unit_interval Real) (x : punctured Real n) :
  punctured_val (radial_mix t x) = mix t (punctured_val x) (punctured_radial_point x).
Proof. reflexivity. Qed.

Lemma radial_mix_start n (x : punctured Real n) : radial_mix (interval_zero Real) x = x.
Proof. apply val_inj; exact: mix_start. Qed.

Lemma radial_mix_end n (x : punctured Real n) :
  radial_mix (interval_one Real) x = boundary_to_punctured (punctured_radial_boundary x).
Proof. apply val_inj; exact: mix_end. Qed.

Lemma radial_mix_fixed n (t : unit_interval Real) (b : boundary Real n) :
  radial_mix t (boundary_to_punctured b) = boundary_to_punctured b.
Proof.
apply val_inj.
change (mix t (val b)
  (radial_projection (@punctured_property Real n (boundary_to_punctured b))) = val b).
rewrite (radial_projection_fixes_boundary _ (set_valP b)); exact: mix_fixed.
Qed.

Lemma uniform_radial_gap n : radial_gap (uniform_simplex Real n) = 0.
Proof.
have hm : coordinate_minimum (uniform_simplex Real n) = (n.+1%:R : Real)^-1.
  have [i hi] := coordinate_minimum_attained (uniform_simplex Real n).
  by rewrite hi uniform_simplex_coordinate.
rewrite /radial_gap hm mulfV ?subrr //; by rewrite pnatr_eq0.
Qed.

Lemma punctured_set_gap n : @punctured_set Real n = [set x : simplex Real n | 0 < radial_gap x].
Proof.
apply/seteqP; split=> x hx; first exact: radial_gap_pos hx.
change (is_true (0 < radial_gap x)) in hx.
change (x <> uniform_simplex Real n); move=> e.
by rewrite e uniform_radial_gap ltxx in hx.
Qed.

Theorem punctured_set_open n : open (@punctured_set Real n).
Proof.
rewrite punctured_set_gap.
apply: (@open_comp (simplex_space Real n) Real (@radial_gap Real n) [set r : Real | 0 < r]).
- move=> x _; exact: radial_gap_continuous.
exact: open_gt.
Qed.

End Geometry.
End DPSingularSimplexRadialDeformationGeometry.


