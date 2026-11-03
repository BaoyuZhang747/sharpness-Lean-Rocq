(** Actual limits of arbitrary diagrams of arbitrary MathComp modules.
    The carrier is the submodule of compatible families in an unrestricted
    dependent product. There is no finite-generation or finite-index premise. *)

From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryLimits CategoryLimitMaps
  CategoryModules CategoryModuleProducts ModuleInfrastructure MackeyModuleCarriers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ModuleLimit.
Variable R : pzRingType.
Variable C : category.
Variable F : module_diagram R C.

Definition module_limit_compatible (x : module_product_type (fobj F)) : Prop :=
  forall i j (f : hom C i j), module_hom_fun (fmap F f) (x i) = x j.

Definition module_limit_subspace : module_subspace (module_product_type (fobj F)).
Proof.
  refine (@ModuleSubspace R (module_product_type (fobj F))
    module_limit_compatible _ _ _).
  - intros i j f. apply module_hom_zero.
  - intros x y hx hy i j f.
    change (module_hom_fun (fmap F f) (x i + y i) = x j + y j).
    rewrite module_hom_add (hx i j f) (hy i j f). reflexivity.
  - intros a x hx i j f.
    change (module_hom_fun (fmap F f) (a *: x i) = a *: x j).
    rewrite module_hom_scale (hx i j f). reflexivity.
Defined.

Definition module_limit_type : lmodType R :=
  [the lmodType R of submodule_carrier module_limit_subspace].

Definition module_limit_val (x : module_limit_type) :
    module_product_type (fobj F) := submodule_val x.

Lemma module_limit_val_linear : linear module_limit_val.
Proof. exact: submodule_val_linear. Qed.

Lemma module_limit_val_injective : injective module_limit_val.
Proof. exact: submodule_val_injective. Qed.

Lemma module_limit_val_compatible (x : module_limit_type) :
    module_limit_compatible (module_limit_val x).
Proof.
  exact (@submodule_val_mem R (module_product_type (fobj F)) module_limit_subspace x).
Qed.

Definition module_limit_projection (i : C) : module_hom module_limit_type (fobj F i).
Proof.
  exists (fun x => module_limit_val x i). intros a x y.
  rewrite module_limit_val_linear. reflexivity.
Defined.

Definition module_limit_cone : cone F module_limit_type.
Proof.
  refine (@Build_cone C (module_category R) F module_limit_type
    module_limit_projection _).
  intros i j f. apply module_hom_ext. intro x.
  exact (module_limit_val_compatible x f).
Defined.

Definition module_limit_lift_fun (U : lmodType R) (s : cone F U) (u : U) :
    module_limit_type.
Proof.
  refine (@submodule_in R (module_product_type (fobj F)) module_limit_subspace
    (fun i => module_hom_fun (cone_leg s i) u) _).
  intros i j f.
  exact (f_equal (fun k : module_hom U (fobj F j) => k u) (cone_natural s f)).
Defined.

Definition module_limit_lift (U : lmodType R) (s : cone F U) :
    module_hom U module_limit_type.
Proof.
  exists (module_limit_lift_fun s). intros a x y.
  apply module_limit_val_injective.
  rewrite module_limit_val_linear.
  apply functional_extensionality_dep. intro i.
  exact (module_hom_linear (cone_leg s i) a x y).
Defined.

(** This supplies existence, factorization, and uniqueness for every
    competing cone, rather than assuming completeness as a field. *)
Definition module_limit : limiting_cone F.
Proof.
  refine (@Build_limiting_cone C (module_category R) F module_limit_type
    module_limit_cone module_limit_lift _ _).
  - intros U s i. apply module_hom_ext. intro u. reflexivity.
  - intros U s f h. apply module_hom_ext. intro u.
    apply module_limit_val_injective.
    apply functional_extensionality_dep. intro i.
    exact (f_equal (fun k : module_hom U (fobj F i) => k u) (h i)).
Defined.

End ModuleLimit.

Arguments module_limit_type {R C} F.
Arguments module_limit_val {R C F} x.
Arguments module_limit {R C} F.
