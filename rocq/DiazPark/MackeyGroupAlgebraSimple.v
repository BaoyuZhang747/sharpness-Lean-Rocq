From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import ModuleInfrastructure MackeyGroupAction
  MackeyGroupAlgebra MackeyGroupAlgebraModule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Simplicity quantifies over all ordinary, Prop-valued submodules. *)
Definition module_is_simple (A : pzRingType) (W : lmodType A) :=
  (exists x : W, x <> 0) /\ forall N : module_subspace W,
    (forall x, N x -> x = 0) \/ (forall x, N x).

Section SimpleGroupModule.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable V : lmodType R.
Variable rho : right_linear_action G V.
Let W := group_algebra_module rho.

Definition group_submodule_underlying (N : module_subspace W) : module_subspace V.
Proof.
refine (@ModuleSubspace R V (fun x => N x) _ _ _).
- exact: subspace_zero.
- move=> x y hx hy; exact: subspace_add hx hy.
- move=> c x hx.
  have h := @subspace_scale [the pzRingType of group_algebra R G] W N
    (c *: group_basis R 1%g) x hx.
  by rewrite group_algebra_module_scalar in h.
Defined.

Lemma group_submodule_underlying_invariant N :
    action_invariant rho (group_submodule_underlying N).
Proof.
move=> g x hx; change (N (right_action rho g x)).
rewrite -(@group_algebra_module_right_action R G V rho g x).
exact (@subspace_scale [the pzRingType of group_algebra R G] W N (group_basis R g^-1) x hx).
Qed.

Definition invariant_group_submodule (N : module_subspace V)
    (hN : action_invariant rho N) : module_subspace W.
Proof.
refine (@ModuleSubspace [the pzRingType of group_algebra R G] W
  (fun x => N x) _ _ _).
- exact: subspace_zero.
- move=> x y hx hy; exact: subspace_add hx hy.
- move=> a x hx; change (N (group_action_scale rho a x)).
  rewrite /group_action_scale; apply: big_ind => [|u v hu hv|g _].
  + exact: subspace_zero.
  + exact: subspace_add hu hv.
  + apply: subspace_scale; exact: hN.
Defined.

Theorem action_simple_group_algebra_iff :
    action_simple rho <-> module_is_simple W.
Proof.
split.
- move=> [hnz hs]; split; first exact hnz.
  move=> N; exact (hs (group_submodule_underlying N) (@group_submodule_underlying_invariant N)).
- move=> [hnz hs]; split; first exact hnz.
  move=> N hN; exact: hs (invariant_group_submodule hN).
Qed.

End SimpleGroupModule.




