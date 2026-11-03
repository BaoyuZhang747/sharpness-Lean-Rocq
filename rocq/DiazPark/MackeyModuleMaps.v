From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SubmoduleMaps.
Variable R : pzRingType.

Definition submodule_inclusion (V : lmodType R) (N : module_subspace V) :
    {linear submodule_carrier N -> V} :=
  (val : {linear submodule_carrier N -> V}).

Variables V W : lmodType R.
Variable f : {linear V -> W}.
Variables (N : module_subspace V) (P : module_subspace W).
Hypothesis hf : forall x, N x -> P (f x).

Definition submodule_map_fun (x : submodule_carrier N) : submodule_carrier P :=
  @submodule_in R W P (f (submodule_val x))
    (@hf _ (submodule_val_mem x)).

Lemma submodule_map_val x :
  submodule_val (submodule_map_fun x) = f (submodule_val x).
Proof. reflexivity. Qed.

Lemma submodule_map_linear : linear submodule_map_fun.
Proof.
move=> a x y; apply (@submodule_val_injective R W P).
change (f (submodule_inclusion N (a *: x + y)) =
  submodule_inclusion P (a *: submodule_map_fun x + submodule_map_fun y)).
by rewrite !linearP /=.
Qed.

HB.instance Definition _ := GRing.isLinear.Build R
  (submodule_carrier N) (submodule_carrier P) _
  submodule_map_fun submodule_map_linear.

Definition submodule_map :
  {linear submodule_carrier N -> submodule_carrier P} := submodule_map_fun.

Lemma submodule_mapE x :
  submodule_inclusion P (submodule_map x) = f (submodule_inclusion N x).
Proof. reflexivity. Qed.

End SubmoduleMaps.

Section QuotientMaps.
Variable R : pzRingType.
Variables V W : lmodType R.
Variable f : {linear V -> W}.
Variables (N : module_subspace V) (P : module_subspace W).
Hypothesis hf : forall x, N x -> P (f x).

Definition quotient_map_base_fun (x : V) : module_quotient P := quotient_pi P (f x).

Lemma quotient_map_base_linear : linear quotient_map_base_fun.
Proof. by move=> a x y; rewrite /quotient_map_base_fun !linearP. Qed.

HB.instance Definition _ := GRing.isLinear.Build R V
  (module_quotient P) _ quotient_map_base_fun quotient_map_base_linear.

Definition quotient_map_base : {linear V -> module_quotient P} :=
  quotient_map_base_fun.

Lemma quotient_map_zero x : N x -> quotient_map_base x = 0.
Proof. move=> hx; apply/(quotient_pi_kernel P (f x)); exact: hf hx. Qed.

Definition quotient_map : {linear module_quotient N -> module_quotient P} :=
  (@quotient_lift R V N (module_quotient P) quotient_map_base
    quotient_map_zero : {linear module_quotient N -> module_quotient P}).

Lemma quotient_map_pi x : quotient_map (quotient_pi N x) = quotient_pi P (f x).
Proof. exact: quotient_lift_pi. Qed.

End QuotientMaps.

Section Exactness.
Variable R : pzRingType.
Variable V : lmodType R.
Variable N : module_subspace V.

Lemma submodule_quotient_exact :
  linear_exact (submodule_inclusion N)
    (quotient_pi N : {linear V -> module_quotient N}).
Proof.
move=> x; rewrite quotient_pi_kernel.
exact: submodule_val_range.
Qed.

End Exactness.

Section KernelImage.
Variable R : pzRingType.
Variables V W : lmodType R.
Variable f : {linear V -> W}.

Definition linear_to_image_fun (x : V) : submodule_carrier (linear_image f) :=
  @submodule_in R W (linear_image f) (f x) (ex_intro _ x (erefl _)).

Lemma linear_to_image_linear : linear linear_to_image_fun.
Proof.
move=> a x y; apply (@submodule_val_injective R W (linear_image f)).
change (f (a *: x + y) = submodule_inclusion (linear_image f)
  (a *: linear_to_image_fun x + linear_to_image_fun y)).
by rewrite !linearP /=.
Qed.

HB.instance Definition _ := GRing.isLinear.Build R V
  (submodule_carrier (linear_image f)) _ linear_to_image_fun linear_to_image_linear.

Definition linear_to_image : {linear V -> submodule_carrier (linear_image f)} :=
  linear_to_image_fun.

Lemma linear_to_image_factor x :
  submodule_inclusion (linear_image f) (linear_to_image x) = f x.
Proof. reflexivity. Qed.

Lemma linear_to_image_surjective : forall y, exists x, linear_to_image x = y.
Proof.
move=> y; have [x hx] := submodule_val_mem y.
exists x; apply (@submodule_val_injective R W (linear_image f)); exact: hx.
Qed.

Lemma linear_to_image_zero x : linear_to_image x = 0 <-> f x = 0.
Proof.
split.
- move=> hx; have h := congr1 (submodule_inclusion (linear_image f)) hx.
  by rewrite linear_to_image_factor linear0 in h.
- move=> hx; apply (@submodule_val_injective R W (linear_image f)).
  change (f x = submodule_inclusion (linear_image f) 0).
  by rewrite linear0 hx.
Qed.

Lemma linear_kernel_image_exact :
  linear_exact (submodule_inclusion (linear_kernel f)) linear_to_image.
Proof.
move=> x; rewrite linear_to_image_zero.
exact: (submodule_val_range (linear_kernel f) x).
Qed.

End KernelImage.
