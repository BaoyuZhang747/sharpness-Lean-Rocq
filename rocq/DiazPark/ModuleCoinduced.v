(** The actual coinduced left R-module Hom_Z(R,J). The action is
    (a*f)(s)=f(s*a), so no commutativity of R is needed. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModules ModuleInjectives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation "M ^z" := (zmodule M) : type_scope.

Lemma integer_scalerE (U : lmodType int) (n : int) (x : U) :
    n *: x = x *~ n.
Proof. have h := @scaler_int int U n x. by rewrite intz in h. Qed.

Section AdditiveToInteger.
Variables U V : lmodType int.
Variable f : U -> V.
Hypothesis hf : additive f.
HB.instance Definition _ := GRing.isAdditive.Build U V f hf.

Lemma integer_linear_of_additive : linear f.
Proof. intros n x y. by rewrite !integer_scalerE raddfD raddfMz. Qed.

Definition integer_hom_of_additive : module_hom U V :=
  exist _ f integer_linear_of_additive.
End AdditiveToInteger.

Section Coinduced.
Variable R : pzRingType.
Variable J : lmodType int.

Record coinduced_data := Coinduced {
  coinduced_fun : R -> J;
  coinduced_additive : additive coinduced_fun
}.

Definition coinduced := classicType coinduced_data.
HB.instance Definition _ := Choice.on coinduced.
Coercion coinduced_fun : coinduced_data >-> Funclass.

Lemma coinduced_ext (f g : coinduced) : (forall s, f s = g s) -> f = g.
Proof.
  destruct f as [f hf], g as [g hg]. simpl. intro h.
  have he : f = g := funext h. destruct he. f_equal. apply Prop_irrelevance.
Qed.

Definition coinduced_zero : coinduced.
Proof. exists (fun _ => 0). by intros s t; rewrite subrr. Defined.

Definition coinduced_add (f g : coinduced) : coinduced.
Proof.
  exists (fun s => f s + g s). intros s t.
  rewrite !coinduced_additive opprD. apply addrACA.
Defined.

Definition coinduced_opp (f : coinduced) : coinduced.
Proof. exists (fun s => - f s). intros s t. by rewrite coinduced_additive opprB opprK addrC. Defined.

Lemma coinduced_addA : associative coinduced_add.
Proof. intros f g h. apply coinduced_ext. intro s. exact (addrA (f s) (g s) (h s)). Qed.
Lemma coinduced_addC : commutative coinduced_add.
Proof. intros f g. apply coinduced_ext. intro s. exact (addrC (f s) (g s)). Qed.
Lemma coinduced_add0 : left_id coinduced_zero coinduced_add.
Proof. intro f. apply coinduced_ext. intro s. exact (add0r (f s)). Qed.
Lemma coinduced_addN : left_inverse coinduced_zero coinduced_opp coinduced_add.
Proof. intro f. apply coinduced_ext. intro s. exact (addNr (f s)). Qed.

HB.instance Definition _ := GRing.isZmodule.Build coinduced
  coinduced_addA coinduced_addC coinduced_add0 coinduced_addN.

Definition coinduced_scale (a : R) (f : coinduced) : coinduced.
Proof. exists (fun s => f (s*a)). intros s t. by rewrite mulrBl coinduced_additive. Defined.

Lemma coinduced_scaleA a b f :
    coinduced_scale a (coinduced_scale b f) = coinduced_scale (a*b) f.
Proof. apply coinduced_ext. intro s. change (f ((s*a)*b) = f (s*(a*b))). by rewrite mulrA. Qed.
Lemma coinduced_scale1 : left_id 1 coinduced_scale.
Proof. intro f. apply coinduced_ext. intro s. change (f (s*1) = f s). by rewrite mulr1. Qed.
Lemma coinduced_scaleD : right_distributive coinduced_scale +%R.
Proof. intros a f g. apply coinduced_ext. intro s. reflexivity. Qed.
Lemma coinduced_scaleDl f a b :
    coinduced_scale (a+b) f = coinduced_scale a f + coinduced_scale b f.
Proof.
  apply coinduced_ext. intro s. change (f (s*(a+b)) = f (s*a) + f (s*b)).
  have hf := @integer_linear_of_additive [the lmodType int of R^z] J f
    (coinduced_additive f).
  have h := hf 1 (s*a) (s*b). rewrite !scale1r in h. by rewrite mulrDr.
Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R coinduced
  coinduced_scaleA coinduced_scale1 coinduced_scaleD coinduced_scaleDl.

Definition coinduced_module : lmodType R := [the lmodType R of coinduced].

Lemma coinduced_add_at (f g : coinduced_module) s : (f+g) s = f s+g s.
Proof. reflexivity. Qed.
Lemma coinduced_scale_at (a : R) (f : coinduced_module) s : (a*:f) s = f (s*a).
Proof. reflexivity. Qed.

End Coinduced.

