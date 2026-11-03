From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleMaps MackeyFiniteGeneration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

(** Right group actions by linear automorphisms on arbitrary modules. *)
Record right_linear_action (R : pzRingType) (G : finGroupType) (V : lmodType R) := {
  right_action : G -> {linear V -> V};
  right_action_one : forall x, right_action 1%g x = x;
  right_action_mul : forall a b x,
    right_action (a*b)%g x = right_action b (right_action a x)
}.

Arguments right_action {R G V} _ _.
Arguments right_action_one {R G V} _ _.
Arguments right_action_mul {R G V} _ _ _ _.

Section ActionTheory.
Variable R : pzRingType.
Variable G : finGroupType.
Variable V : lmodType R.
Variable rho : right_linear_action G V.

Lemma right_action_cancel g : cancel (right_action rho g) (right_action rho g^-1).
Proof. by move=> x; rewrite -right_action_mul mulgV right_action_one. Qed.

Lemma right_action_injective g : injective (right_action rho g).
Proof. exact: can_inj (right_action_cancel g). Qed.

Definition action_invariant (N : module_subspace V) :=
  forall g x, N x -> N (right_action rho g x).

Definition action_simple := (exists x : V, x <> 0) /\
  forall N : module_subspace V, action_invariant N ->
    (forall x, N x -> x = 0) \/ (forall x, N x).

Variable v : V.

Definition action_orbit_span : module_subspace V :=
  span_subspace (fun x => exists g : G, right_action rho g v = x).

Lemma action_orbit_span_contains : action_orbit_span v.
Proof. apply: span_generator; exists 1%g; exact: right_action_one. Qed.

Lemma action_orbit_span_invariant : action_invariant action_orbit_span.
Proof.
move=> g x hx; elim: hx => [y [h <-]| |y z hy ihy hz ihz|a y hy ihy].
- apply: span_generator; exists (h*g)%g; exact: right_action_mul.
- rewrite linear0; exact: span_zero.
- rewrite linearD; exact: span_add.
- rewrite linearZ; exact: span_scale.
Qed.

Lemma action_orbit_span_finitely_generated :
    module_finitely_generated [the lmodType R of submodule_carrier action_orbit_span].
Proof.
apply: (@finite_spanning_submodule R V action_orbit_span G
  (fun g => right_action rho g v)).
- move=> g; apply: span_generator; by exists g.
- by move=> x hx.
Qed.

End ActionTheory.

Section InvariantSubmodule.
Variable R : pzRingType.
Variable G : finGroupType.
Variable V : lmodType R.
Variable rho : right_linear_action G V.
Variable N : module_subspace V.
Hypothesis hN : action_invariant rho N.

Definition submodule_right_action : right_linear_action G
    [the lmodType R of submodule_carrier N].
Proof.
refine (@Build_right_linear_action R G _
  (fun g => @submodule_map R V V (right_action rho g) N N (hN g)) _ _).
- move=> x; apply: submodule_val_injective; exact: right_action_one.
- move=> a b x; apply: submodule_val_injective; exact: right_action_mul.
Defined.

Lemma submodule_right_action_val g x :
    submodule_val (right_action submodule_right_action g x) =
      right_action rho g (submodule_val x).
Proof. reflexivity. Qed.

End InvariantSubmodule.
