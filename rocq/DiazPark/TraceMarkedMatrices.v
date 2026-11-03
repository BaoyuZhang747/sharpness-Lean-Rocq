From mathcomp Require Import all_boot all_algebra.

(** The determinant step for integral Burnside marks.  In particular, the
    mark matrix is only assumed to have nonzero determinant; it is never
    assumed invertible.  These statements do not identify the coefficient
    module with a finite-dimensional representation. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section IntegralMarks.

Variable R : idomainType.
Variable n : nat.

(** A nonzero determinant suffices for injectivity of the column mark map,
    by the adjugate identity and cancellation in the integral domain. *)
Lemma trace_mark_matrix_injective (T : 'M[R]_n) :
    \det T != 0 -> injective (fun v : 'cV[R]_n => T *m v).
Proof.
move=> hT v w h.
have h' := congr1 (fun A : 'cV[R]_n => \adj T *m A) h.
rewrite !mulmxA mul_adj_mx !mul_scalar_mx in h'.
apply/matrixP=> i j; apply: (mulfI hT).
have hentry := congr1 (fun A : 'cV[R]_n => A i j) h'.
by move: hentry; rewrite !mxE.
Qed.

(** The intertwining identity comes from multiplicativity of actual marks.
    This lemma performs only the integral determinant cancellation step. *)
Lemma trace_mark_determinant (T L : 'M[R]_n) (d : 'rV[R]_n) :
    \det T != 0 -> T *m L = diag_mx d *m T ->
    \det L = \prod_i d 0 i.
Proof.
move=> hT h.
have hdet := congr1 (fun A : 'M[R]_n => \det A) h.
rewrite !det_mulmx det_diag in hdet.
apply: (mulfI hT).
by rewrite hdet mulrC.
Qed.

(** Unit marks give an invertible multiplication matrix.  This does not
    assert that the mark matrix T is invertible over the base domain. *)
Lemma trace_unit_marks_unit_matrix (T L : 'M[R]_n) (d : 'rV[R]_n) :
    \det T != 0 -> T *m L = diag_mx d *m T ->
    (forall i, d 0 i \is a GRing.unit) -> L \in unitmx.
Proof.
move=> hT h hd.
rewrite unitmxE (trace_mark_determinant hT h).
by apply: unitr_prod => i _; exact: hd i.
Qed.

Lemma trace_unit_marks_inverse (T L : 'M[R]_n) (d : 'rV[R]_n) :
    \det T != 0 -> T *m L = diag_mx d *m T ->
    (forall i, d 0 i \is a GRing.unit) ->
    L *m invmx L = 1%:M /\ invmx L *m L = 1%:M.
Proof.
move=> hT h hd.
have hL := trace_unit_marks_unit_matrix hT h hd.
by split; [exact: mulmxV hL | exact: mulVmx hL].
Qed.

End IntegralMarks.

Print Assumptions trace_mark_matrix_injective.
Print Assumptions trace_mark_determinant.
Print Assumptions trace_unit_marks_unit_matrix.
Print Assumptions trace_unit_marks_inverse.
