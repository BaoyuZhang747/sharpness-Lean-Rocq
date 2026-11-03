(** Coefficient-natural module formulas for the actual Kan extensions of
    a fibration and its fiber inclusion. *)
From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryLimits CategoryExtensionality CategoryNaturalIso
  CategoryComma CategoryStructured CategoryFibration CategoryFiberRan CategoryFiberLan
  CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor CategoryModuleRightKan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition module_ran_fiber_iso (R : pzRingType) {C D : category} {p : functor C D}
    (hp : fibration p) (b : D) (M : module_diagram R C) :
    @isomorphism (module_category R) (fobj (fobj (module_ran R p) M) b)
      (module_limit_type (functor_comp (fiber_inclusion p b) M)) :=
  fiber_ran_limit_iso hp b M
    (module_limit (functor_comp (structured_projection p b) M))
    (module_limit (functor_comp (fiber_inclusion p b) M)).
Arguments module_ran_fiber_iso R {C D p} hp b M.

Definition module_ran_fiber_nat_iso (R : pzRingType) {C D : category} {p : functor C D}
    (hp : fibration p) (b : D) :
    @isomorphism
      (functor_category (functor_category C (module_category R)) (module_category R))
      (functor_comp (module_ran R p) (evaluation_functor D (module_category R) b))
      (functor_comp (precomposition (module_category R) (fiber_inclusion p b))
        (module_limit_functor R (fiber_category p b))).
Proof.
refine (@nat_iso_of_components (functor_category C (module_category R)) (module_category R)
  (functor_comp (module_ran R p) (evaluation_functor D (module_category R) b))
  (functor_comp (precomposition (module_category R) (fiber_inclusion p b))
    (module_limit_functor R (fiber_category p b)))
  (module_ran_fiber_iso R hp b) _).
intros M N t.
exact (@fiber_ran_limit_iso_natural C D (module_category R) p hp b M N t
  (module_limit (functor_comp (structured_projection p b) M))
  (module_limit (functor_comp (structured_projection p b) N))
  (module_limit (functor_comp (fiber_inclusion p b) M))
  (module_limit (functor_comp (fiber_inclusion p b) N))).
Defined.

Lemma module_ran_fiber_iso_coordinate (R : pzRingType) {C D : category} {p : functor C D}
    (hp : fibration p) (b : D) (M : module_diagram R C) (x : fiber_category p b) :
    @compose (module_category R) _ _ _ (iso_hom (module_ran_fiber_iso R hp b M))
      (cone_leg (limit_cone (module_limit (functor_comp (fiber_inclusion p b) M))) x) =
    cone_leg (limit_cone (module_limit (functor_comp (structured_projection p b) M)))
      (fiber_structured_point x).
Proof.
exact (fiber_ran_limit_hom_fac b M
  (module_limit (functor_comp (structured_projection p b) M))
  (module_limit (functor_comp (fiber_inclusion p b) M)) x).
Qed.

Definition module_fiber_lan_sum_nat_iso (R : pzRingType) {C D : category} {p : functor C D}
    (hp : fibration p) (b : D) (a : C) :
    @isomorphism
      (functor_category (functor_category (fiber_category p b) (module_category R))
        (module_category R))
      (functor_comp (@fiber_lan R C D p hp b) (evaluation_functor C (module_category R) a))
      (fiber_lan_sum_functor R hp b a).
Proof.
refine (@nat_iso_of_components
  (functor_category (fiber_category p b) (module_category R)) (module_category R)
  (functor_comp (@fiber_lan R C D p hp b) (evaluation_functor C (module_category R) a))
  (fiber_lan_sum_functor R hp b a) (fun M => @fiber_lan_sum_iso R C D p hp b M a) _).
intros M N t. exact (@fiber_lan_sum_iso_natural R C D p hp b a M N t).
Defined.
