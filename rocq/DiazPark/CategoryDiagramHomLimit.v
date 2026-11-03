(** Evaluation at one identifies Hom from the constant regular module with
    the actual module of compatible families, naturally in the coefficient. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryDiagramHom CategoryModuleProducts CategoryModuleLimits
  CategoryModuleLimitFunctor HomologicalDiagramLimits MackeyModuleCarriers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition constant_regular_diagram (R : comPzRingType) (C : category) : module_diagram R C.
Proof.
refine (@Build_functor C (module_category R) (fun _ => [the lmodType R of R^o])
  (fun _ _ _ => module_hom_id _) _ _).
- intro x; reflexivity.
- intros x y z f g; apply module_hom_ext; intro a; reflexivity.
Defined.
Arguments constant_regular_diagram R C : clear implicits.

Section ConstantHom.
Variable R : comPzRingType.
Variable C : category.
Variable D : module_diagram R C.

Definition constant_hom_to_limit (f : diagram_hom_type (constant_regular_diagram R C) D) :
    module_limit_type D.
Proof.
refine (@submodule_in R (module_product_type (fobj D)) (module_limit_subspace D)
  (fun x => diagram_hom_at f x 1) _).
intros x y u.
exact (Logic.eq_sym (congr1 (fun h : module_hom [the lmodType R of R^o] (fobj D y) => h 1)
  (naturality f u))).
Defined.
Lemma constant_hom_to_limit_linear : linear constant_hom_to_limit.
Proof.
intros a f g; apply module_limit_val_injective; apply functional_extensionality_dep; intro x.
reflexivity.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R
  (diagram_hom_type (constant_regular_diagram R C) D) (module_limit_type D) _
  constant_hom_to_limit constant_hom_to_limit_linear.

Definition regular_to_module (V : lmodType R) (v : V) : module_hom [the lmodType R of R^o] V.
Proof.
exists (fun a => a *: v). intros a b c.
change ((a * b + c) *: v = a *: (b *: v) + c *: v).
by rewrite scalerDl scalerA.
Defined.

Definition constant_hom_from_limit (v : module_limit_type D) :
    diagram_hom_type (constant_regular_diagram R C) D.
Proof.
refine (@Build_nat_trans C (module_category R) (constant_regular_diagram R C) D
  (fun x => regular_to_module (module_limit_val v x)) _).
intros x y u; apply module_hom_ext; intro a.
change (a *: module_limit_val v y = module_hom_fun (fmap D u) (a *: module_limit_val v x)).
rewrite module_hom_scale (module_limit_val_compatible v u). reflexivity.
Defined.
Lemma constant_hom_from_limit_linear : linear constant_hom_from_limit.
Proof.
intros a f g; apply diagram_hom_ext; intros x v.
change (v *: (a *: module_limit_val f x + module_limit_val g x) =
  a *: (v *: module_limit_val f x) + v *: module_limit_val g x).
by rewrite scalerDr !scalerA mulrC.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (module_limit_type D)
  (diagram_hom_type (constant_regular_diagram R C) D) _
  constant_hom_from_limit constant_hom_from_limit_linear.

Lemma constant_hom_from_to f : constant_hom_from_limit (constant_hom_to_limit f) = f.
Proof.
apply diagram_hom_ext; intros x a.
change (a *: module_hom_fun (component f x) 1 = module_hom_fun (component f x) a).
rewrite -module_hom_scale.
change (module_hom_fun (component f x) (a * 1) = module_hom_fun (component f x) a).
by rewrite mulr1.
Qed.
Lemma constant_hom_to_from v : constant_hom_to_limit (constant_hom_from_limit v) = v.
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep; intro x.
change (1 *: module_limit_val v x = module_limit_val v x); exact: scale1r.
Qed.

Definition constant_hom_limit_iso : @isomorphism (module_category R)
    (diagram_hom_type (constant_regular_diagram R C) D) (module_limit_type D).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear constant_hom_to_limit) (module_hom_of_linear constant_hom_from_limit) _ _).
- apply module_hom_ext; exact: constant_hom_from_to.
- apply module_hom_ext; exact: constant_hom_to_from.
Defined.
End ConstantHom.

Lemma constant_hom_limit_naturality {R : comPzRingType} {C : category}
    {D E : module_diagram R C} (u : nat_trans D E)
    (f : diagram_hom_type (constant_regular_diagram R C) D) :
    constant_hom_to_limit (diagram_hom_post (constant_regular_diagram R C) u f) =
      limit_action u (constant_hom_to_limit f).
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep; intro x.
rewrite limit_action_coordinate; reflexivity.
Qed.

Definition constant_hom_limit_nat_iso (R : comPzRingType) (C : category) :
    @isomorphism (functor_category (functor_category C (module_category R)) (module_category R))
      (diagram_hom_functor (constant_regular_diagram R C)) (module_limit_functor R C).
Proof.
refine (@nat_iso_of_components (functor_category C (module_category R)) (module_category R) (diagram_hom_functor (constant_regular_diagram R C)) (module_limit_functor R C) (fun D => constant_hom_limit_iso D) _).
intros D E u; apply module_hom_ext; exact: constant_hom_limit_naturality.
Defined.


