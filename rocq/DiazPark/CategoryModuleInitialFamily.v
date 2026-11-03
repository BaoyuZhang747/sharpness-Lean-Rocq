(** A module diagram on a category with a discrete initial family has
    limit the unrestricted product of its values on that family. *)
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryLimits CategoryLimitMaps
  CategoryInitialFamily CategoryModules CategoryModuleProducts
  CategoryModuleLimits CategoryExtensionality CategoryNaturalIso
  CategoryModuleLimitFunctor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section InitialFamilyLimit.
Variable R : pzRingType.
Variable C : category.
Variable T : initial_family C.
Variable F : module_diagram R C.

Definition initial_family_product : lmodType R :=
  module_product_type (fun i => fobj F (initial_family_object T i)).

Definition initial_family_leg_at (x : C)
    (z : {i : initial_family_index T & hom C (initial_family_object T i) x}) :
    hom (module_category R) initial_family_product (fobj F x) :=
  @compose (module_category R) initial_family_product
    (fobj F (initial_family_object T (projT1 z))) (fobj F x)
    (module_product_projection _ (projT1 z)) (fmap F (projT2 z)).

Definition initial_family_leg (x : C) :
    hom (module_category R) initial_family_product (fobj F x) :=
  initial_family_leg_at (initial_family_choice T x).

Lemma initial_family_leg_natural x y (f : hom C x y) :
  compose (initial_family_leg x) (fmap F f) = initial_family_leg y.
Proof.
  unfold initial_family_leg.
  rewrite <- (initial_family_choice_natural T f).
  unfold initial_family_leg_at, initial_family_compose. simpl.
  rewrite fmap_compose. apply module_hom_ext. intro v. reflexivity.
Qed.

Definition initial_family_cone : cone F initial_family_product :=
  @Build_cone C (module_category R) F initial_family_product
    initial_family_leg initial_family_leg_natural.

Lemma initial_family_leg_self i :
  initial_family_leg (initial_family_object T i) =
    module_product_projection _ i.
Proof.
  unfold initial_family_leg. rewrite initial_family_choice_self.
  unfold initial_family_leg_at. simpl. rewrite fmap_id.
  apply module_hom_ext. intro v. reflexivity.
Qed.

Definition initial_family_lift (V : lmodType R) (s : cone F V) :
    module_hom V initial_family_product :=
  module_product_lift (fun i => cone_leg s (initial_family_object T i)).

Lemma initial_family_lift_fac (V : lmodType R) (s : cone F V) x :
  @compose (module_category R) V initial_family_product (fobj F x)
    (initial_family_lift s) (initial_family_leg x) = cone_leg s x.
Proof.
  unfold initial_family_leg, initial_family_leg_at.
  destruct (initial_family_choice T x) as [i f]. simpl.
  apply module_hom_ext. intro v.
  exact (f_equal (fun h : module_hom V (fobj F x) => h v)
    (cone_natural s f)).
Qed.

Definition initial_family_limit : limiting_cone F.
Proof.
  refine (@Build_limiting_cone C (module_category R) F
    initial_family_product initial_family_cone
    (fun V s => initial_family_lift s) initial_family_lift_fac _).
  intros V s f hf. apply module_product_hom_ext. intro i.
  specialize (hf (initial_family_object T i)).
  change (compose f (initial_family_leg (initial_family_object T i)) =
    cone_leg s (initial_family_object T i)) in hf.
  rewrite initial_family_leg_self in hf.
  rewrite module_product_lift_fac. exact hf.
Defined.

Definition module_initial_family_iso :
    @isomorphism (module_category R) (module_limit_type F)
      initial_family_product :=
  limit_unique_iso (module_limit F) initial_family_limit.

Lemma module_initial_family_iso_coordinate i :
  @compose (module_category R) (module_limit_type F) initial_family_product
    (fobj F (initial_family_object T i))
    (iso_hom module_initial_family_iso) (module_product_projection _ i) =
    module_limit_projection F (initial_family_object T i).
Proof.
  pose proof (limit_map_fac (module_limit F) initial_family_limit
    (nat_id F) (initial_family_object T i)) as h.
  change (compose (iso_hom module_initial_family_iso)
    (initial_family_leg (initial_family_object T i)) =
    @compose (module_category R) (module_limit_type F)
      (fobj F (initial_family_object T i)) (fobj F (initial_family_object T i))
      (module_limit_projection F (initial_family_object T i))
      (identity (fobj F (initial_family_object T i)))) in h.
  rewrite initial_family_leg_self compose_id_right in h. exact h.
Qed.

End InitialFamilyLimit.

Arguments initial_family_product {R C} T F.
Arguments initial_family_limit {R C} T F.
Arguments module_initial_family_iso {R C} T F.

Section CoefficientNaturality.
Variable R : pzRingType.
Variable C : category.
Variable T : initial_family C.

Definition initial_family_product_functor :
    functor (functor_category C (module_category R)) (module_category R).
Proof.
  refine (@Build_functor (functor_category C (module_category R))
    (module_category R) (fun F => initial_family_product T F)
    (fun F G a => module_product_map
      (fun i => component a (initial_family_object T i))) _ _).
  - intro F. apply module_hom_ext. intro v.
    apply functional_extensionality_dep. intro i. reflexivity.
  - intros F G H a b. apply module_hom_ext. intro v.
    apply functional_extensionality_dep. intro i. reflexivity.
Defined.

Definition module_initial_family_nat_iso :
    @isomorphism
      (functor_category (functor_category C (module_category R)) (module_category R))
      (module_limit_functor R C) initial_family_product_functor.
Proof.
  refine (@nat_iso_of_components (functor_category C (module_category R))
    (module_category R) (module_limit_functor R C) initial_family_product_functor
    (fun F => module_initial_family_iso T F) _).
  intros F G a. apply module_product_hom_ext. intro i.
  change (compose
    (compose (limit_map (module_limit F) (module_limit G) a)
      (iso_hom (module_initial_family_iso T G)))
    (module_product_projection _ i) =
    compose (compose (iso_hom (module_initial_family_iso T F))
      (module_product_map (fun i => component a (initial_family_object T i))))
      (module_product_projection _ i)).
  rewrite compose_assoc module_initial_family_iso_coordinate.
  rewrite limit_map_fac.
  apply module_hom_ext. intro v.
  pose proof (f_equal
    (fun h : module_hom (module_limit_type F) (fobj F (initial_family_object T i)) => h v)
    (@module_initial_family_iso_coordinate R C T F i)) as h.
  exact (f_equal (module_hom_fun (component a (initial_family_object T i))) (Logic.eq_sym h)).
Defined.

End CoefficientNaturality.

Arguments initial_family_product_functor R {C} T.
Arguments module_initial_family_nat_iso R {C} T.
