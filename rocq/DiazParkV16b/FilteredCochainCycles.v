(** Actual filtered-cycle submodules for an integer decreasing filtration of
    a nonnegative cochain complex. The structure assumes only filtration and
    differential preservation, never exactness, pages or convergence. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological.
Local Open Scope ring_scope.

Module DPFilteredCycles.
Section Filtered.
Variable R : pzRingType.
Variable C : cochain_complex R.

Record cochain_filtration := CochainFiltration {
  filtration : forall (p : Z) n, module_subspace (cochain_term C n);
  filtration_decreasing : forall p q n, Z.le p q -> subspace_le (filtration q n) (filtration p n);
  filtration_d : forall p n x, filtration p n x -> filtration p n.+1 (cochain_d C n x)
}.

Variable F : cochain_filtration.

Definition almost_cycles (r : nat) (p : Z) n : module_subspace (cochain_term C n) :=
  subspace_inter (filtration F p n)
    (linear_preimage (cochain_d C n) (filtration F (Z.add p (Z.of_nat r)) n.+1)).

Definition filtered_boundary_condition (s : Z) n : cochain_term C n -> Prop :=
  match n as k return cochain_term C k -> Prop with
  | O => fun x => x = 0
  | S k => fun x => exists y, filtration F s k y /\ cochain_d C k y = x
  end.
Arguments filtered_boundary_condition s n x : clear implicits.

Definition filtered_boundary_subspace (s : Z) n : module_subspace (cochain_term C n).
Proof.
refine (@ModuleSubspace R (cochain_term C n) (filtered_boundary_condition s n) _ _ _).
- destruct n; [reflexivity|]; exists 0; split; [exact: subspace_zero|exact: linear0].
- destruct n; simpl.
  + intros x y -> ->; exact: addr0.
  + intros x y [a [ha <-]] [b [hb <-]]; exists (a+b); split.
    * exact: subspace_add ha hb.
    * exact: linearD.
- destruct n; simpl.
  + intros a x ->; exact: scaler0.
  + intros a x [y [hy <-]]; exists (a *: y); split.
    * exact (@subspace_scale R (cochain_term C n) (filtration F s n) a y hy).
    * exact: linearZ.
Defined.

Definition filtered_boundaries (r : nat) (p : Z) n : module_subspace (cochain_term C n) :=
  subspace_inter (filtration F p n) (filtered_boundary_subspace (Z.sub p (Z.of_nat r)) n).

Lemma filtered_boundary_d_zero s n x : filtered_boundary_condition s n x -> cochain_d C n x = 0.
Proof. destruct n; simpl; [intro hx; by rewrite hx linear0|intros [y [hy <-]]; exact: cochain_d2]. Qed.

Lemma almost_cycles_mono r s p n (h : (r <= s)%coq_nat) :
    subspace_le (almost_cycles s p n) (almost_cycles r p n).
Proof.
intros x [hx hdx]; split; first exact hx.
apply: (@filtration_decreasing F (Z.add p (Z.of_nat r)) (Z.add p (Z.of_nat s)) n.+1 _ _ hdx); lia.
Qed.

Lemma almost_cycles_d r p n x : almost_cycles r p n x ->
    almost_cycles r (Z.add p (Z.of_nat r)) n.+1 (cochain_d C n x).
Proof.
intros [hx hdx]; split; [exact hdx|].
change (filtration F (Z.add (Z.add p (Z.of_nat r)) (Z.of_nat r)) n.+2
  (cochain_d C n.+1 (cochain_d C n x))).
rewrite cochain_d2; exact: subspace_zero.
Qed.

Lemma filtered_boundaries_are_almost_cycles r s p n :
    subspace_le (filtered_boundaries r p n) (almost_cycles s p n).
Proof.
intros x [hx hb]; split; [exact hx|].
change (filtration F (Z.add p (Z.of_nat s)) n.+1 (cochain_d C n x)).
rewrite (filtered_boundary_d_zero hb); exact: subspace_zero.
Qed.

Lemma next_column_almost_cycles r p n :
    subspace_le (almost_cycles r (Z.succ p) n) (almost_cycles r.+1 p n).
Proof.
intros x [hx hdx]; split.
- apply: (@filtration_decreasing F p (Z.succ p) n _ _ hx); lia.
- change (filtration F (Z.add p (Z.of_nat r.+1)) n.+1 (cochain_d C n x)).
  have he : Z.add p (Z.of_nat r.+1) = Z.add (Z.succ p) (Z.of_nat r) by lia.
  by rewrite he.
Qed.

End Filtered.
End DPFilteredCycles.
