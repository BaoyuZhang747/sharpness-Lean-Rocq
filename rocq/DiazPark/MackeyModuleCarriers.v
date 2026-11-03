From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp ring_quotient.
From DiazPark Require Import ModuleInfrastructure.

(** Classical packaging is isolated here.  The imported boolp foundation
    provides functional/propositional extensionality and indefinite
    description.  No mathematical axiom about modules is introduced.
    All coefficient rings below may be the zero ring. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section BareModulePackaging.
Variable R : pzRingType.

(** An ordinary module, before equality and choice structures are supplied. *)
Record bare_module := BareModule {
  bare_carrier : Type;
  bare_zero : bare_carrier;
  bare_add : bare_carrier -> bare_carrier -> bare_carrier;
  bare_opp : bare_carrier -> bare_carrier;
  bare_scale : R -> bare_carrier -> bare_carrier;
  bare_addA : associative bare_add;
  bare_addC : commutative bare_add;
  bare_add0 : left_id bare_zero bare_add;
  bare_addN : left_inverse bare_zero bare_opp bare_add;
  bare_scaleA : forall a b x,
    bare_scale a (bare_scale b x) = bare_scale (a * b) x;
  bare_scale1 : left_id 1 bare_scale;
  bare_scaleD : right_distributive bare_scale bare_add;
  bare_scaleDl : forall x a b,
    bare_scale (a + b) x = bare_add (bare_scale a x) (bare_scale b x)
}.

Variable A : bare_module.

Definition classical_module := classicType (bare_carrier A).
HB.instance Definition _ := Choice.on classical_module.
HB.instance Definition _ := GRing.isZmodule.Build classical_module
  (@bare_addA A) (@bare_addC A) (@bare_add0 A) (@bare_addN A).
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R classical_module
  (@bare_scaleA A) (@bare_scale1 A) (@bare_scaleD A) (@bare_scaleDl A).

(** The packaging does not replace the carrier or its operations. *)
Lemma classical_module_carrier : classical_module = bare_carrier A.
Proof. reflexivity. Qed.

Lemma classical_module_scale a (x : classical_module) :
  a *: x = @bare_scale A a x.
Proof. reflexivity. Qed.

End BareModulePackaging.

Section SubmoduleCarrier.
Variable R : pzRingType.
Variable V : lmodType R.
Variable N : module_subspace V.

Definition subspace_pred (x : V) : bool := `[< N x >].

Lemma subspace_predP x : reflect (N x) (subspace_pred x).
Proof. exact: asboolP. Qed.

Lemma subspace_pred_closed : submod_closed subspace_pred.
Proof.
split.
- apply/subspace_predP; exact: subspace_zero.
- move=> a x y /subspace_predP hx /subspace_predP hy.
  apply/subspace_predP; apply: subspace_add _ hy.
  exact (@subspace_scale R V N a x hx).
Qed.

HB.instance Definition _ :=
  GRing.isSubmodClosed.Build R V subspace_pred subspace_pred_closed.

Record submodule_carrier := SubmoduleCarrier {
  submodule_val : V;
  submodule_property : subspace_pred submodule_val
}.

HB.instance Definition _ := [isSub for submodule_val].
HB.instance Definition _ := [Choice of submodule_carrier by <:].
HB.instance Definition _ := [SubChoice_isSubLmodule of submodule_carrier by <:].

Lemma submodule_val_mem (x : submodule_carrier) : N (submodule_val x).
Proof. apply/subspace_predP; exact: submodule_property. Qed.

Definition submodule_in (x : V) (hx : N x) : submodule_carrier :=
  @SubmoduleCarrier x (asboolT hx).

Lemma submodule_in_val x (hx : N x) : submodule_val (submodule_in hx) = x.
Proof. reflexivity. Qed.

Lemma submodule_val_linear : linear submodule_val.
Proof. change (linear (val : submodule_carrier -> V)); exact: linearP. Qed.

Lemma submodule_val_injective : injective submodule_val.
Proof. exact: val_inj. Qed.

Lemma submodule_val_range x :
  N x <-> exists y : submodule_carrier, submodule_val y = x.
Proof.
split.
- move=> hx; by exists (submodule_in hx).
- by move=> [y <-]; exact: submodule_val_mem.
Qed.

End SubmoduleCarrier.
