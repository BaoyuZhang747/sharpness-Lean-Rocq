From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import TraceCharacteristic.

(** Actual finite-group right-coset sums.  The subgroup need not be normal,
    and the target additive group need not be finite or finitely generated. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Section RightCosetTrace.

Variables (gT : finGroupType) (V : zmodType).
Variables G H : {group gT}.
Hypothesis subgroup_le : H \subset G.
Variable f : gT -> V.
Hypothesis left_invariant : forall h, h \in H -> forall x, x \in G ->
  f (h * x)%g = f x.

Lemma trace_one_right_coset x : x \in G ->
    \sum_(y in H :* x) f y = f x *+ #|H|.
Proof.
move=> Gx.
transitivity (\sum_(y in H :* x) f x).
- apply: eq_bigr => y /rcosetP[h Hh ->].
  exact: left_invariant h Hh x Gx.
- by rewrite sumr_const card_rcoset.
Qed.

(** The index set is MathComp's genuine set of right cosets, and repr is
    its actual representative operation. The equality is a proved finite
    sum identity, not an assumed Mackey or trace formula. *)
Lemma trace_right_coset_regroup :
    \sum_(x in G) f x =
      (\sum_(X in rcosets H G) f (repr X)) *+ #|H|.
Proof.
rewrite (partition_big_imset (rcoset H)) /= -sumrMnl.
apply: eq_bigr => X /rcosetsP[x Gx ->].
have hpred : forall y,
    ((y \in G) && (rcoset H y == H :* x)) = (y \in H :* x).
  move=> y; rewrite rcosetE (sameP eqP rcoset_eqP).
  apply/andP/idP=> [[_ hy]|hy]; first exact: hy.
  split=> //.
  case/rcosetP: hy => h Hh ->.
  exact: groupM (subsetP subgroup_le h Hh) Gx.
rewrite (eq_bigl (fun y => y \in H :* x) f hpred) (trace_one_right_coset Gx).
congr (_ *+ _).
case: (repr_rcosetP H x) => h Hh.
by rewrite left_invariant.
Qed.

Lemma trace_right_coset_sum_zero p :
    (forall v : V, v *+ p = 0) -> (p %| #|H|)%N ->
    \sum_(x in G) f x = 0.
Proof.
move=> hp hcard; rewrite trace_right_coset_regroup.
exact (@trace_dvdn_mul_zero V p hp #|H| _ hcard).
Qed.

End RightCosetTrace.

Section CharacteristicRightCosetTrace.

Variables (gT : finGroupType) (R : pzRingType) (V : lmodType R).
Variables G H : {group gT}.
Variable f : gT -> V.

Lemma trace_char_right_coset_sum_zero p :
    p%:R = (0 : R) -> H \subset G -> (p %| #|H|)%N ->
    (forall h, h \in H -> forall x, x \in G -> f (h * x)%g = f x) ->
    \sum_(x in G) f x = 0.
Proof.
move=> hp hHG hcard hinvariant.
exact (@trace_right_coset_sum_zero gT _ G H hHG f hinvariant p
  (@trace_char_mul_zero R V p hp) hcard).
Qed.

End CharacteristicRightCosetTrace.

Section RightActionTrace.

Variables (gT : finGroupType) (V : zmodType).
Variables G H : {group gT}.
Hypothesis action_subgroup_le : H \subset G.
Variable rho : V -> gT -> V.
Hypothesis right_action_mul : forall v a b, a \in G -> b \in G ->
  rho (rho v a) b = rho v (a * b)%g.
Hypothesis subgroup_acts_trivially : forall v h, h \in H -> rho v h = v.

(** Only the multiplication law is needed for this summation statement.
    An actual linear right action supplies this law; neither finite
    dimensionality nor a separately postulated trace identity is used. *)
Lemma trace_trivial_subgroup_regroup (v : V) :
    \sum_(x in G) rho v x =
      (\sum_(X in rcosets H G) rho v (repr X)) *+ #|H|.
Proof.
apply (@trace_right_coset_regroup gT V G H action_subgroup_le (rho v)).
move=> h Hh x Gx.
rewrite -(@right_action_mul v h x (subsetP action_subgroup_le h Hh) Gx).
by rewrite (@subgroup_acts_trivially v h Hh).
Qed.

Lemma trace_trivial_subgroup_zero p (v : V) :
    (forall w : V, w *+ p = 0) -> (p %| #|H|)%N ->
    \sum_(x in G) rho v x = 0.
Proof.
move=> hp hcard; rewrite trace_trivial_subgroup_regroup.
exact (@trace_dvdn_mul_zero V p hp #|H| _ hcard).
Qed.

End RightActionTrace.

Print Assumptions trace_one_right_coset.
Print Assumptions trace_right_coset_regroup.
Print Assumptions trace_right_coset_sum_zero.
Print Assumptions trace_char_right_coset_sum_zero.
Print Assumptions trace_trivial_subgroup_regroup.
Print Assumptions trace_trivial_subgroup_zero.
