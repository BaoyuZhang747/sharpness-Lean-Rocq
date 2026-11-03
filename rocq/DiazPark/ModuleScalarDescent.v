(** A genuine module action over a quotient ring, constructed from an
    arbitrary surjective ring map whose kernel annihilates the module. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalScalarRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkScalarRestriction.
Local Open Scope ring_scope.

Module DPScalarDescent.
Section Descent.
Variables A B : pzRingType.
Variable phi : {rmorphism A -> B}.
Hypothesis onto : forall b, exists a, phi a = b.
Definition scalar_lift b : A := proj1_sig (constructive_indefinite_description (onto b)).
Lemma scalar_lift_spec b : phi (scalar_lift b) = b.
Proof. exact: (proj2_sig (constructive_indefinite_description (onto b))). Qed.

Section Module.
Variable V : lmodType A.
Hypothesis annihilates : forall a, phi a = 0 -> forall x : V, a *: x = 0.

Lemma equal_scalar_action a b (x : V) : phi a = phi b -> a *: x = b *: x.
Proof.
move=> hab.
have hz : phi (a-b) = 0 by rewrite rmorphB hab subrr.
have hx := annihilates hz x.
rewrite scalerBl in hx; exact: subr0_eq hx.
Qed.

Definition descended_module :=
  let _ := phi in let _ := onto in let _ := annihilates in (V : Type).
HB.instance Definition _ := GRing.Zmodule.on descended_module.
Definition descended_scale (b : B) (x : descended_module) : descended_module :=
  scalar_lift b *: (x : V).

Lemma descended_scale_from a (x : V) : descended_scale (phi a) x = a *: x.
Proof. apply: equal_scalar_action; exact: scalar_lift_spec. Qed.
Lemma descended_scaleA a b x :
  descended_scale a (descended_scale b x) = descended_scale (a*b) x.
Proof.
rewrite /descended_scale scalerA; apply: equal_scalar_action.
by rewrite rmorphM !scalar_lift_spec.
Qed.
Lemma descended_scale1 : left_id 1 descended_scale.
Proof. move=> x; rewrite -(rmorph1 phi) descended_scale_from; exact: scale1r. Qed.
Lemma descended_scaleD : right_distributive descended_scale +%R.
Proof. move=> b x y; exact: scalerDr. Qed.
Lemma descended_scaleDl x a b :
  descended_scale (a+b) x = descended_scale a x + descended_scale b x.
Proof.
rewrite /descended_scale -scalerDl; apply: equal_scalar_action.
by rewrite rmorphD !scalar_lift_spec.
Qed.
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build B descended_module
  descended_scaleA descended_scale1 descended_scaleD descended_scaleDl.
Definition descended_module_type : lmodType B := [the lmodType B of descended_module].

Lemma descent_forward_linear : forall (a : A) (x y : V), (a *: x + y : V) =
    (a *: (x : restricted_module_type phi descended_module_type) + y).
Proof.
move=> a x y; change (a *: x + y = descended_scale (phi a) x + y).
by rewrite descended_scale_from.
Qed.
Lemma descent_inverse_linear : forall (a : A) (x y : restricted_module_type phi descended_module_type),
    (a *: x + y : restricted_module_type phi descended_module_type) =
    (a *: (x : V) + y : V).
Proof. move=> a x y; exact: esym (descent_forward_linear a x y). Qed.

Definition descent_restriction_iso : @isomorphism (module_category A) V
    (restricted_module_type phi descended_module_type).
Proof.
refine (@Build_isomorphism (module_category A) V
  (restricted_module_type phi descended_module_type)
  (exist _ (fun x => x) descent_forward_linear)
  (exist _ (fun x => x) descent_inverse_linear) _ _);
  apply module_hom_ext => x; reflexivity.
Defined.
End Module.

Section Map.
Variables U V : lmodType A.
Hypothesis hU : forall a, phi a = 0 -> forall x : U, a *: x = 0.
Hypothesis hV : forall a, phi a = 0 -> forall x : V, a *: x = 0.
Variable f : {linear U -> V}.
Definition descended_linear_fun (x : descended_module_type hU) : descended_module_type hV := f x.
Lemma descended_linearP : linear descended_linear_fun.
Proof. move=> b x y; exact: linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build B (descended_module_type hU)
  (descended_module_type hV) _ descended_linear_fun descended_linearP.
Definition descended_linear : {linear descended_module_type hU -> descended_module_type hV} :=
  descended_linear_fun.
End Map.
End Descent.
End DPScalarDescent.
