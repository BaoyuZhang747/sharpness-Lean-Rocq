(** A uniform ball refinement of an actual open cover of a compact metric set. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype sequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularSubdivisionSmallnessCompact.
Section CompactCover.
Variable Real : realType.
Variable M : pseudoMetricType Real.
Variable I : Type.
Variable U : I -> set M.

Lemma compact_open_cover_uniform_ball (K : set M) (hK : compact K)
    (hopen : forall i, open (U i))
    (hcover : forall x, K x -> exists i, U i x) :
  exists2 eps : Real, 0 < eps &
    forall x, K x -> exists i, ball x eps `<=` U i.
Proof.
pose P := fun r : nat => fun x : M =>
  exists i, ball x (@harmonic Real r) `<=` U i.
have hlocal : forall x, K x ->
    \forall y \near x & r \near \oo, P r y.
  move=> x hx; case: (hcover x hx) => i hxi.
  have hxU : nbhs x (U i).
    by move: (hopen i); rewrite openE => /(_ x hxi).
  case/nbhs_ballP: hxU => e he hball.
  have he2 : 0 < e / 2 by rewrite divr_gt0 // ltr0n.
  have hsmall : \forall r \near \oo, @harmonic Real r < e / 2.
    have h := cvgr0_norm_lt (@harmonic Real) cvg_harmonic (e / 2) he2.
    case: h => N _ hN; exists N => // r hr.
    have hh := hN r hr.
    by rewrite ger0_norm ?harmonic_ge0 in hh.
  change (filter_prod (nbhs x) eventually
    (fun yr : M * nat => P yr.2 yr.1)).
  exists (ball x (e / 2), [set r : nat | @harmonic Real r < e / 2]).
  - split; [exact: nbhsx_ballx he2 | exact: hsmall].
  - move=> [y r] [hxy hr]; exists i => z hyz; apply: hball.
    apply: (@ball_split Real M y x z e hxy).
    exact (@le_ball Real M y (@harmonic Real r) (e / 2) (ltW hr) z hyz).
have hnear : \forall r \near \oo, forall x, K x -> P r x.
  exact: (proj1 (compact_near_coveringP K) hK _ _ _ _ hlocal).
case: hnear => N _ hN.
exists (@harmonic Real N); first exact: harmonic_gt0.
by move=> x hx; exact: (hN N (leqnn N) x hx).
Qed.

End CompactCover.
End DPSingularSubdivisionSmallnessCompact.
