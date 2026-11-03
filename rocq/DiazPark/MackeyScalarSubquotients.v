From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient MackeyModuleMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ScalarSubquotients.
Variable R : comPzRingType.
Variable V : lmodType R.
Variable r : R.
Local Notation K := (@scalar_kernel R V r).
Local Notation I := (@scalar_image R V r).

Definition scalar_to_image_fun (x : V) : submodule_carrier I :=
  @submodule_in R V I (r *: x) (ex_intro _ x (erefl _)).

Lemma scalar_to_image_linear : linear scalar_to_image_fun.
Proof.
move=> a x y; apply (@submodule_val_injective R V I).
change (r *: (a *: x + y) = submodule_inclusion I
  (a *: scalar_to_image_fun x + scalar_to_image_fun y)).
by rewrite scalerDr linearP /= !scalerA [r * a]mulrC.
Qed.

HB.instance Definition _ := GRing.isLinear.Build R V
  (submodule_carrier I) _ scalar_to_image_fun scalar_to_image_linear.

Definition scalar_to_image : {linear V -> submodule_carrier I} :=
  scalar_to_image_fun.

Lemma scalar_to_image_factor x :
  submodule_inclusion I (scalar_to_image x) = r *: x.
Proof. reflexivity. Qed.

Lemma scalar_to_image_surjective : forall y, exists x, scalar_to_image x = y.
Proof.
move=> y; have [x hx] := submodule_val_mem y.
exists x; apply (@submodule_val_injective R V I); exact: hx.
Qed.

Lemma scalar_to_image_zero x : scalar_to_image x = 0 <-> r *: x = 0.
Proof.
split.
- move=> hx; have h := congr1 (submodule_inclusion I) hx.
  by rewrite scalar_to_image_factor linear0 in h.
- move=> hx; apply (@submodule_val_injective R V I).
  change (r *: x = submodule_inclusion I 0).
  by rewrite linear0 hx.
Qed.

Lemma scalar_kernel_image_exact :
  linear_exact (submodule_inclusion K) scalar_to_image.
Proof.
move=> x; rewrite scalar_to_image_zero.
exact: (submodule_val_range K x).
Qed.

(** These are the actual two scalar short exact sequences, not existence
    assertions for unrelated abstract modules or maps. *)
Lemma scalar_kernel_image_short_exact :
  injective (submodule_inclusion K) /\
  linear_exact (submodule_inclusion K) scalar_to_image /\
  (forall y, exists x, scalar_to_image x = y).
Proof.
split; first exact: submodule_val_injective.
split; [exact: scalar_kernel_image_exact | exact: scalar_to_image_surjective].
Qed.

Lemma scalar_image_quotient_short_exact :
  injective (submodule_inclusion I) /\
  linear_exact (submodule_inclusion I)
    (quotient_pi I : {linear V -> module_quotient I}) /\
  (forall y, exists x, quotient_pi I x = y).
Proof.
split; first exact: submodule_val_injective.
split; [exact: submodule_quotient_exact | exact: quotient_pi_surjective].
Qed.

End ScalarSubquotients.
