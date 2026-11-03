(** Finite atomic filtration by the support of a coefficient diagram. The
    induction concerns objects, never dimension or cardinality of values. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryFinite CategoryModules
  CategoryAtomicDeletionCore CategoryAtomicDeletionAdjunction CategoryAtomicDeletionSequence
  HomologicalComplex BarComplex BarNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkBarComplex DiazParkBarNaturality.
Local Open Scope ring_scope.

Section RankedCategory.
Variable C : finite_category.
Variable rank : fc_object C -> nat.
Hypothesis rank_mono : forall x y, fc_hom C x y -> (rank x <= rank y)%N.
Hypothesis rank_equal_iso : forall x y, fc_hom C x y -> rank x = rank y -> @fc_isomorphic C x y.
Local Notation CC := (fc_category C).

Lemma rank_isomorphic x y : @fc_isomorphic C x y -> rank x = rank y.
Proof.
move=> h; apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: (rank_mono (iso_hom (fc_iso_of_related h))).
- exact: (rank_mono (iso_inv (fc_iso_of_related h))).
Qed.

Definition atomic_upper_away (q x : fc_object C) : Prop :=
  (rank q <= rank x)%N /\ ~ @fc_isomorphic C x q.

Lemma atomic_upper_away_upward q (x y : CC) (f : hom CC x y) :
  atomic_upper_away q x -> atomic_upper_away q y.
Proof.
move=> [hqx hxq]; split; first exact: leq_trans hqx (rank_mono f).
move=> hyq.
have hyr := rank_isomorphic hyq.
have hxy : rank x = rank y.
  apply/eqP; rewrite eqn_leq; apply/andP; split; first exact: rank_mono f.
  by rewrite hyr.
exact (hxq (fc_isomorphic_trans (rank_equal_iso f hxy) hyq)).
Qed.

Lemma atomic_upper_away_self q : ~ atomic_upper_away q q.
Proof. move=> [_ h]; exact (h (@fc_isomorphic_refl C q)). Qed.

Variable R : pzRingType.

Definition coefficient_nonzero (D : module_codiagram R CC) (x : fc_object C) : bool :=
  asbool (exists v : fobj D x, v <> 0).

Lemma coefficient_zeroP (D : module_codiagram R CC) x :
  ~ coefficient_nonzero D x <-> forall v : fobj D x, v = 0.
Proof.
split.
- move=> h v; case: (pselect (v = 0)) => // hv.
  exfalso; apply h; apply/asboolP; exists v; exact hv.
- move=> h /asboolP [v hv]; exact (hv (h v)).
Qed.

Definition coefficient_support_size (D : module_codiagram R CC) := #|coefficient_nonzero D|.

Definition coefficient_atomic (D : module_codiagram R CC) q : Prop :=
  forall x, ~ @fc_isomorphic C x q -> forall v : fobj D x, v = 0.

Lemma atomic_deletion_smaller (D : module_codiagram R CC) q : coefficient_nonzero D q ->
  (coefficient_support_size (deletion_truncation (@atomic_upper_away_upward q) D) <
    coefficient_support_size D)%N.
Proof.
move=> hq; apply proper_card; apply/properP; split.
- apply/subsetP => x hx.
  apply/asboolP; case: (pselect (exists v : fobj D x, v <> 0)) => // hn.
  exfalso.
  have hz : forall v : fobj D x, v = 0.
    move=> v; case: (pselect (v = 0)) => // hv; exfalso; apply hn; exists v; exact hv.
  have hx0 := @deletion_truncation_of_zero R CC (atomic_upper_away q)
    (@atomic_upper_away_upward q) D x hz.
  move/asboolP: hx => [v hv]; exact (hv (hx0 v)).
- exists q; first exact hq.
  apply/negP; move/asboolP=> [v hv].
  exact (hv (@deletion_truncation_outside R CC (atomic_upper_away q) (@atomic_upper_away_upward q) D q
    (@atomic_upper_away_self q) v)).
Qed.

Lemma minimal_deletion_kernel_atomic (D : module_codiagram R CC) q :
  (forall x, coefficient_nonzero D x -> (rank q <= rank x)%N) ->
  coefficient_atomic (deletion_kernel (@atomic_upper_away_upward q) D) q.
Proof.
move=> hmin x hxq.
case hx: (coefficient_nonzero D x).
- apply deletion_kernel_inside; split; [exact: hmin | exact hxq].
- apply deletion_kernel_of_zero; apply/coefficient_zeroP.
  by rewrite hx.
Qed.

Lemma pointwise_zero_bar (D : module_codiagram R CC) :
  (forall x (v : fobj D x), v = 0) -> all_degree_acyclic (bar_complex D).
Proof.
move=> h n a ha.
have hz : a = 0.
  apply functional_extensionality_dep => x; apply functional_extensionality_dep => path; exact: h.
rewrite hz; move: a ha hz; case: n => [|n] a ha hz; first reflexivity.
exists 0; exact: linear0.
Qed.

Variable H : fc_object C -> Prop.
Hypothesis atom_acyclic : forall q, ~ H q -> forall D : module_codiagram R CC,
  coefficient_atomic D q -> all_degree_acyclic (bar_complex D).

Theorem finite_atomic_deletion (D : module_codiagram R CC) :
  (forall x, H x -> forall v : fobj D x, v = 0) -> all_degree_acyclic (bar_complex D).
Proof.
have step : forall n (E : module_codiagram R CC), (coefficient_support_size E < n)%N ->
    (forall x, H x -> forall v : fobj E x, v = 0) -> all_degree_acyclic (bar_complex E).
  elim=> [|n ih] E hn hE; first by rewrite ltn0 in hn.
  case: (pselect (exists q, coefficient_nonzero E q)) => [[q0 hq0]|hzero].
  - have [q hq hmin] := @arg_minnP (fc_object C) q0 (coefficient_nonzero E) rank hq0.
    have nq : ~ H q.
      move=> hH; have hz := hE q hH; move/asboolP: hq => [v hv]; exact (hv (hz v)).
    pose E' := deletion_truncation (@atomic_upper_away_upward q) E.
    have hsize : (coefficient_support_size E' < n)%N.
      exact: leq_trans (atomic_deletion_smaller hq) hn.
    have hE' : all_degree_acyclic (bar_complex E').
      apply: (ih E' hsize) => x hx; exact: deletion_truncation_of_zero (hE x hx).
    have hK : all_degree_acyclic (bar_complex (deletion_kernel (@atomic_upper_away_upward q) E)).
      apply: (@atom_acyclic q nq (deletion_kernel (@atomic_upper_away_upward q) E)).
      exact: minimal_deletion_kernel_atomic hmin.
    exact: all_degree_acyclic_extension (deletion_bar_short_exact (@atomic_upper_away_upward q) E) hK hE'.
  - apply pointwise_zero_bar => x; apply/coefficient_zeroP => hx; apply hzero; exists x; exact hx.
move=> hD; apply: (step (coefficient_support_size D).+1 D _ hD); exact: ltnSn.
Qed.

End RankedCategory.
