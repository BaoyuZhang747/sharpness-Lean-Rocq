From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp ring_quotient.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers.

(** The quotient of an arbitrary module by an arbitrary Prop-valued
    submodule.  The additive quotient is the actual MathComp quotient;
    its scalar action is constructed and proved well defined below. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Section ModuleQuotient.
Variable R : pzRingType.
Variable V : lmodType R.
Variable N : module_subspace V.

Definition reflected_subspace : zmodClosed V :=
  HB.pack (subspace_pred N)
    (GRing.isZmodClosed.Build V (subspace_pred N)
      (GRing.submod_closedB (subspace_pred_closed N))).

Definition module_quotient := @Quotient.quot V reflected_subspace.

HB.instance Definition _ := GRing.Zmodule.on module_quotient.

Definition quotient_pi (x : V) : module_quotient := \pi x.

Lemma quotient_pi_repr (x : module_quotient) : quotient_pi (repr x) = x.
Proof. exact: reprK. Qed.

Lemma quotient_pi_eq x y :
  (quotient_pi x == quotient_pi y) = subspace_pred N (x - y).
Proof. by rewrite /quotient_pi piE. Qed.

Lemma quotient_pi_zero : quotient_pi 0 = 0.
Proof. by rewrite /quotient_pi piE. Qed.

Lemma quotient_pi_add x y : quotient_pi (x + y) = quotient_pi x + quotient_pi y.
Proof. by rewrite /quotient_pi piE. Qed.

Lemma quotient_pi_kernel x : quotient_pi x = 0 <-> N x.
Proof.
split.
- move=> hx; apply/subspace_predP.
  have he : quotient_pi x == quotient_pi 0.
    by apply/eqP; rewrite quotient_pi_zero.
  by move: he; rewrite quotient_pi_eq subr0.
- move=> hx; apply/eqP.
  rewrite -quotient_pi_zero quotient_pi_eq subr0.
  by apply/subspace_predP.
Qed.

Definition quotient_scale (a : R) (x : module_quotient) : module_quotient :=
  quotient_pi (a *: repr x).

Lemma quotient_scale_pi a x :
  quotient_scale a (quotient_pi x) = quotient_pi (a *: x).
Proof.
apply/eqP; rewrite /quotient_scale quotient_pi_eq -scalerBr.
apply/subspace_predP; apply: subspace_scale.
apply/subspace_predP; rewrite -quotient_pi_eq quotient_pi_repr.
exact: eqxx.
Qed.

Lemma quotient_scaleA a b x :
  quotient_scale a (quotient_scale b x) = quotient_scale (a * b) x.
Proof.
by rewrite -[x]quotient_pi_repr !quotient_scale_pi scalerA.
Qed.

Lemma quotient_scale1 : left_id 1 quotient_scale.
Proof. by move=> x; rewrite -[x]quotient_pi_repr quotient_scale_pi scale1r. Qed.

Lemma quotient_scaleDr : right_distributive quotient_scale +%R.
Proof.
move=> a x y; rewrite -[x]quotient_pi_repr -[y]quotient_pi_repr.
by rewrite -quotient_pi_add !quotient_scale_pi scalerDr quotient_pi_add.
Qed.

Lemma quotient_scaleDl x a b :
  quotient_scale (a + b) x = quotient_scale a x + quotient_scale b x.
Proof.
by rewrite -[x]quotient_pi_repr !quotient_scale_pi scalerDl quotient_pi_add.
Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R module_quotient
  quotient_scaleA quotient_scale1 quotient_scaleDr quotient_scaleDl.

Lemma quotient_pi_linear : linear quotient_pi.
Proof.
move=> a x y; rewrite quotient_pi_add.
by rewrite -quotient_scale_pi.
Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R V module_quotient _ quotient_pi quotient_pi_linear.

Lemma quotient_pi_surjective : forall y, exists x, quotient_pi x = y.
Proof. by move=> x; exists (repr x); exact: quotient_pi_repr. Qed.

Section UniversalMap.
Variable W : lmodType R.
Variable f : {linear V -> W}.
Hypothesis fN : forall x, N x -> f x = 0.

Definition quotient_lift (_ : forall x, N x -> f x = 0)
    (x : module_quotient) : W := f (repr x).

Lemma quotient_lift_pi x : quotient_lift fN (quotient_pi x) = f x.
Proof.
have hmem : N (repr (quotient_pi x) - x).
  apply/subspace_predP; rewrite -quotient_pi_eq quotient_pi_repr.
  exact: eqxx.
have hz := @fN _ hmem.
by move/eqP: hz; rewrite linearB subr_eq0 => /eqP.
Qed.

Lemma quotient_lift_linear : linear (quotient_lift fN).
Proof.
move=> a x y; rewrite -[x]quotient_pi_repr -[y]quotient_pi_repr.
change (quotient_lift fN (quotient_scale a (quotient_pi (repr x)) +
  quotient_pi (repr y)) = a *: quotient_lift fN (quotient_pi (repr x)) +
  quotient_lift fN (quotient_pi (repr y))).
by rewrite quotient_scale_pi -quotient_pi_add !quotient_lift_pi linearP.
Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R module_quotient W _ (quotient_lift fN) quotient_lift_linear.

Lemma quotient_lift_unique (g : {linear module_quotient -> W}) :
  (forall x, g (quotient_pi x) = f x) -> forall x, g x = quotient_lift fN x.
Proof. by move=> hg x; rewrite -[x]quotient_pi_repr hg quotient_lift_pi. Qed.

End UniversalMap.
End ModuleQuotient.
