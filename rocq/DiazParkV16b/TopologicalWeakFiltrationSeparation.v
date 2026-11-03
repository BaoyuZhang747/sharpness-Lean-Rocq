(** Closed injections and T1 separation in an actual exhaustive weak filtration.
    The transition-map hypotheses are discharged separately for the skeleta. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalWeakFiltrationSeparation.
Section Filtration.
Variable X : topologicalType.
Variable Y : nat -> topologicalType.
Variable f : forall n, Y n -> X.
Arguments f n : clear implicits.
Variable fi : forall n, injective (f n).
Variable hfinal : forall B : set X, (forall n, closed (f n @^-1` B)) -> closed B.

Lemma weak_filtration_point_closed (hY : forall n, accessible_space (Y n)) (x : X) :
  closed [set x].
Proof.
apply hfinal => n.
case: (pselect (exists y, f n y = x)) => [[y hy]|hn].
- have e : f n @^-1` [set x] = [set y].
    apply/predeqP => z; split.
    + move=> hz; apply (@fi n _ _); exact: etrans hz (esym hy).
    + by move=> ->.
  rewrite e; exact (@accessible_closed_set1 (Y n) (@hY n) y).
- have e : f n @^-1` [set x] = set0.
    apply/predeqP => y; split; last by [].
    move=> hy; exfalso; apply hn; by exists y.
  rewrite e; exact: closed0.
Qed.

Theorem weak_filtration_accessible (hY : forall n, accessible_space (Y n)) :
  accessible_space X.
Proof.
move=> x y hxy; exists (~` [set y]); constructor.
- rewrite openC; exact (@weak_filtration_point_closed hY y).
- by rewrite inE /=; exact/eqP.
- by rewrite inE /=.
Qed.

Variable g : forall n m, (n <= m)%N -> Y n -> Y m.
Arguments g {n m} _ _.
Variable gw : forall n m (h : (n <= m)%N) y, f m (g h y) = f n y.
Variable gc : forall n m (h : (n <= m)%N), continuous (g h).
Variable gclosed : forall n m (h : (n <= m)%N) (S : set (Y n)),
  closed S -> closed (g h @` S).

Lemma weak_filtration_image_preimage_later n m (h : (n <= m)%N) (S : set (Y n)) :
  f m @^-1` (f n @` S) = g h @` S.
Proof.
apply/predeqP => y; split.
- move=> [z hz e]; exists z=> //; apply (@fi m _ _).
  exact: etrans (gw h z) e.
- move=> [z hz <-]; exists z=> //; symmetry; exact: gw.
Qed.

Lemma weak_filtration_image_preimage_earlier n m (h : (m <= n)%N) (S : set (Y n)) :
  f m @^-1` (f n @` S) = g h @^-1` S.
Proof.
apply/predeqP => y; split.
- move=> [z hz e]. have he : g h y = z.
    apply (@fi n _ _); exact: etrans (gw h y) (esym e).
  change (S (g h y)); by rewrite he.
- move=> hy; exists (g h y)=> //; exact: gw.
Qed.

Theorem weak_filtration_stage_closed n (S : set (Y n)) (hS : closed S) :
  closed (f n @` S).
Proof.
apply hfinal => m; case: (leqP n m) => hnm.
- rewrite (weak_filtration_image_preimage_later hnm); exact: gclosed hS.
- have hmn : (m <= n)%N := ltnW hnm.
  rewrite (weak_filtration_image_preimage_earlier hmn).
  apply: preimage_closed; last exact hS.
  by move=> y hy; exact (@gc m n hmn y).
Qed.
End Filtration.
End DPTopologicalWeakFiltrationSeparation.
