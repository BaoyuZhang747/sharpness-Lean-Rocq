From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyGroupAction MackeyGroupAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ActionModule.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable V : lmodType R.
Variable rho : right_linear_action G V.

(** Inversion converts the given right action into a left group-algebra
    module, on exactly the original carrier and additive group. *)
Definition group_action_scale (a : group_algebra R G) (x : V) : V :=
  \sum_g a g *: right_action rho g^-1 x.

Lemma group_action_scale_linear a : linear (group_action_scale a).
Proof.
move=> c x y; rewrite /group_action_scale scaler_sumr -big_split /=.
apply: eq_bigr=> g _; rewrite linearP /= scalerDr !scalerA.
by rewrite mulrC.
Qed.
HB.instance Definition _ a := GRing.isLinear.Build R V V _
  (group_action_scale a) (group_action_scale_linear a).

Definition group_action_scale_flip x a := group_action_scale a x.
Lemma group_action_scale_flip_linear x : linear (group_action_scale_flip x).
Proof.
move=> c a b; rewrite /group_action_scale_flip /group_action_scale.
rewrite scaler_sumr -big_split /=; apply: eq_bigr=> g _.
by rewrite !ffunE group_regular_scale scalerDl scalerA.
Qed.
HB.instance Definition _ x := GRing.isLinear.Build R
  [the lmodType R of group_algebra R G] V _
  (group_action_scale_flip x) (group_action_scale_flip_linear x).

Lemma group_action_scale_basis g x :
    group_action_scale (group_basis R g) x = right_action rho g^-1 x.
Proof.
rewrite /group_action_scale (bigD1 g) //= /group_basis ffunE eqxx scale1r.
rewrite big1 ?addr0 // => h /negbTE hh.
by rewrite ffunE eq_sym hh scale0r.
Qed.

Lemma group_action_scale_scalel c a x :
    group_action_scale (c *: a) x = c *: group_action_scale a x.
Proof. change (group_action_scale_flip x (c *: a) = c *: group_action_scale_flip x a). exact: linearZ. Qed.

Lemma group_action_scale_addl a b x :
    group_action_scale (a + b) x =
      group_action_scale a x + group_action_scale b x.
Proof. change (group_action_scale_flip x (a + b) = group_action_scale_flip x a + group_action_scale_flip x b). exact: linearD. Qed.

Lemma group_action_scale_suml (I : finType) (f : I -> group_algebra R G) x :
    group_action_scale (\sum_i f i) x = \sum_i group_action_scale (f i) x.
Proof. exact: (linear_sum (group_action_scale_flip x) _ _ _). Qed.

Lemma group_action_scaleA a b x :
    group_action_scale a (group_action_scale b x) =
    group_action_scale (a * b) x.
Proof.
change (group_action_scale a (group_action_scale b x) = group_action_scale (group_mul a b) x).
rewrite /group_mul group_action_scale_suml {1}/group_action_scale.
apply: eq_bigr=> g _; rewrite group_action_scale_suml.
rewrite {1}/group_action_scale linear_sum scaler_sumr /=.
apply: eq_bigr=> h _; rewrite group_action_scale_scalel group_action_scale_basis.
by rewrite linearZ /= scalerA invgM right_action_mul.
Qed.
Lemma group_action_scale1 x : group_action_scale 1 x = x.
Proof.
rewrite group_algebra_one group_action_scale_basis invg1.
exact: right_action_one.
Qed.

Definition group_algebra_bare_module :
    @bare_module [the pzRingType of group_algebra R G] :=
  @BareModule [the pzRingType of group_algebra R G] V 0 +%R -%R
    group_action_scale (@addrA V) (@addrC V) (@add0r V) (@addNr V)
    group_action_scaleA group_action_scale1
    (fun a x y => linearD (group_action_scale a) x y)
    (fun x a b => group_action_scale_addl a b x).

Definition group_algebra_module :=
  [the lmodType [the pzRingType of group_algebra R G] of
    classical_module group_algebra_bare_module].
Lemma group_algebra_module_scale (a : group_algebra R G) (x : group_algebra_module) :
    a *: x = group_action_scale a x.
Proof. reflexivity. Qed.

Lemma group_algebra_module_basis g (x : group_algebra_module) :
    group_basis R g *: x = right_action rho g^-1 x.
Proof. exact: group_action_scale_basis. Qed.

Lemma group_algebra_module_right_action g (x : group_algebra_module) :
    group_basis R g^-1 *: x = right_action rho g x.
Proof. by rewrite group_algebra_module_basis invgK. Qed.

Lemma group_algebra_module_scalar c (x : group_algebra_module) :
    (c *: group_basis R 1%g) *: x = (c *: x : V).
Proof.
rewrite group_algebra_module_scale group_action_scale_scalel.
by rewrite group_action_scale_basis invg1 right_action_one.
Qed.

End ActionModule.






