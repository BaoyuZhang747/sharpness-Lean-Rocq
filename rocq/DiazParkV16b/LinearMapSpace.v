(** The actual arbitrary-module Hom module, with evaluation and composition. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import CategoryModuleProducts ModuleInfrastructure MackeyModuleCarriers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPLinearMapSpace.
Section Spaces.
Variable R : comPzRingType.
Variables U V : lmodType R.

Definition function_module : lmodType R := module_product_type (fun _ : U => V).

Definition linear_subspace : module_subspace function_module.
Proof.
refine (@ModuleSubspace R function_module (fun f => linear f) _ _ _).
- move=> a x y; change (0 = a *: (0 : V) + 0).
  by rewrite scaler0 addr0.
- move=> f g hf hg a x y.
  change (f (a *: x + y) + g (a *: x + y) = a *: (f x + g x) + (f y + g y)).
  rewrite hf hg scalerDr. exact: addrACA.
- move=> a f hf b x y.
  change (a *: f (b *: x + y) = b *: (a *: f x) + a *: f y).
  by rewrite hf scalerDr !scalerA (mulrC a b).
Defined.

Definition linear_maps : lmodType R := [the lmodType R of submodule_carrier linear_subspace].
Definition evaluate (f : linear_maps) (x : U) : V := val f x.
Arguments evaluate f x : clear implicits.

Lemma evaluate_is_linear (f : linear_maps) : linear (evaluate f).
Proof. exact (@submodule_val_mem R function_module linear_subspace f). Qed.

HB.instance Definition _ (f : linear_maps) :=
  GRing.isLinear.Build R U V _ (evaluate f) (evaluate_is_linear f).

Definition as_linear (f : linear_maps) : {linear U -> V} := evaluate f.

Lemma ext (f g : linear_maps) : (forall x, evaluate f x = evaluate g x) -> f = g.
Proof.
move=> h; apply submodule_val_injective; apply functional_extensionality_dep; exact h.
Qed.

Lemma evaluate_zero x : evaluate 0 x = 0.
Proof. reflexivity. Qed.
Lemma evaluate_add (f g : linear_maps) x : evaluate (f + g) x = evaluate f x + evaluate g x.
Proof. reflexivity. Qed.
Lemma evaluate_scale a (f : linear_maps) x : evaluate (a *: f) x = a *: evaluate f x.
Proof. reflexivity. Qed.
Lemma evaluate_opp (f : linear_maps) x : evaluate (- f) x = - evaluate f x.
Proof. reflexivity. Qed.

Definition of_linear (f : {linear U -> V}) : linear_maps :=
  @submodule_in R function_module linear_subspace f (linearP f).

Lemma of_linear_evaluate (f : {linear U -> V}) x : evaluate (of_linear f) x = f x.
Proof. reflexivity. Qed.

End Spaces.
Arguments linear_maps {R} U V.
Arguments evaluate {R U V} f x.
Arguments as_linear {R U V} f.
Arguments of_linear {R U V} f.

Section Composition.
Variable R : comPzRingType.
Variables U V W : lmodType R.

Definition precompose_fun (g : {linear W -> U}) (f : linear_maps U V) : linear_maps W V :=
  of_linear (as_linear f \o g : {linear W -> V}).

Lemma precompose_fun_linear (g : {linear W -> U}) : linear (precompose_fun g).
Proof.
move=> a f h; apply ext => x; reflexivity.
Qed.

HB.instance Definition _ (g : {linear W -> U}) :=
  GRing.isLinear.Build R (linear_maps U V) (linear_maps W V) _
    (precompose_fun g) (precompose_fun_linear g).

Definition precompose (g : {linear W -> U}) :
    {linear linear_maps U V -> linear_maps W V} := precompose_fun g.

Lemma precompose_evaluate (g : {linear W -> U}) (f : linear_maps U V) x :
  evaluate (precompose g f) x = evaluate f (g x).
Proof. reflexivity. Qed.

Definition postcompose_fun (g : {linear V -> W}) (f : linear_maps U V) : linear_maps U W :=
  of_linear (g \o as_linear f : {linear U -> W}).

Lemma postcompose_fun_linear (g : {linear V -> W}) : linear (postcompose_fun g).
Proof.
move=> a f h; apply ext => x.
change (g (a *: evaluate f x + evaluate h x) = a *: g (evaluate f x) + g (evaluate h x)).
exact: linearP.
Qed.

HB.instance Definition _ (g : {linear V -> W}) :=
  GRing.isLinear.Build R (linear_maps U V) (linear_maps U W) _
    (postcompose_fun g) (postcompose_fun_linear g).

Definition postcompose (g : {linear V -> W}) :
    {linear linear_maps U V -> linear_maps U W} := postcompose_fun g.

Lemma postcompose_evaluate (g : {linear V -> W}) (f : linear_maps U V) x :
  evaluate (postcompose g f) x = g (evaluate f x).
Proof. reflexivity. Qed.

End Composition.
End DPLinearMapSpace.
