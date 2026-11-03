From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalSimplexBasic TopologicalSimplexContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.

Module DPRealizationBoundaryTopology.

Lemma continuous_injective_hausdorff {X Y : topologicalType} (f : X -> Y)
    (hf : continuous f) (hi : injective f) (hY : hausdorff_space Y) :
  hausdorff_space X.
Proof.
rewrite open_hausdorff in hY. rewrite open_hausdorff.
move=> x y hxy.
have hne : f x != f y by rewrite (inj_eq hi); exact hxy.
have [[U V] [hx hy] [hU hV hUV]] := hY _ _ hne.
exists (f @^-1` U, f @^-1` V).
- split; by rewrite inE in hx hy |- *.
- constructor.
  + exact ((proj1 (continuousP f) hf) U hU).
  + exact ((proj1 (continuousP f) hf) V hV).
  + apply/eqP; apply/seteqP; split=> z; last by [].
    move=> [hz hz']. have h : (U `&` V) (f z) := conj hz hz'.
    by move: h; rewrite (eqP hUV).
Qed.

Lemma subtype_hausdorff {X : topologicalType} (A : set X) (hX : hausdorff_space X) :
  hausdorff_space [the topologicalType of set_type A].
Proof.
apply: (@continuous_injective_hausdorff _ X set_val).
- exact: initial_continuous.
- exact: val_inj.
- exact hX.
Qed.

Lemma compact_inverse_continuous {X Y : topologicalType} (f : X -> Y) (g : Y -> X)
    (hf : continuous f) (hX : @compact X setT) (hY : hausdorff_space Y)
    (hfg : cancel f g) (hgf : cancel g f) : continuous g.
Proof.
apply/(continuous_closedP g) => A hA.
have hcomp : compact A := subclosed_compact hA hX (fun _ _ => I).
have himg : compact (f @` A).
  apply: continuous_compact; [exact: continuous_subspaceT hf | exact hcomp].
have he : g @^-1` A = f @` A.
  apply/seteqP; split=> y hy.
  - exists (g y); first exact hy; exact: hgf.
  - destruct hy as [x hx e]. subst y. change (A (g (f x))). by rewrite hfg.
rewrite he; exact: compact_closed.
Qed.

Lemma coordinate_boundary_hausdorff (Real : realType) n :
  hausdorff_space (DPTopologicalSimplex.boundary_space Real n).
Proof.
apply: subtype_hausdorff. apply: subtype_hausdorff.
exact: norm_hausdorff.
Qed.

End DPRealizationBoundaryTopology.
