(** The actual coefficient-natural module isomorphism
        limit_D (Ran_L M) = limit_C M.
    This is the degree-zero comparison used beneath the resolution argument. *)
From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryLimits CategoryExtensionality
  CategoryComma CategoryStructured CategoryModules CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryNaturalIso CategoryModuleRightKan
  CategoryRightKanLimits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition module_ran_limit_iso (R : pzRingType) {C D : category}
    (L : functor C D) (M : module_diagram R C) :
    @isomorphism (module_category R)
      (module_limit_type (fobj (module_ran R L) M)) (module_limit_type M) :=
  right_kan_limit_iso L M
    (fun d => module_limit (functor_comp (structured_projection L d) M))
    (module_limit M) (module_limit (fobj (module_ran R L) M)).

Arguments module_ran_limit_iso R {C D} L M.

Definition module_ran_limit_nat_iso (R : pzRingType) {C D : category}
    (L : functor C D) :
    @isomorphism
      (functor_category (functor_category C (module_category R)) (module_category R))
      (functor_comp (module_ran R L) (module_limit_functor R D))
      (module_limit_functor R C).
Proof.
  refine (@nat_iso_of_components (functor_category C (module_category R))
    (module_category R)
    (functor_comp (module_ran R L) (module_limit_functor R D))
    (module_limit_functor R C) (module_ran_limit_iso R L) _).
  intros M N t.
  exact (@right_kan_limit_iso_natural C D (module_category R) L M N
    (fun d => module_limit (functor_comp (structured_projection L d) M))
    (fun d => module_limit (functor_comp (structured_projection L d) N))
    (module_limit M) (module_limit N)
    (module_limit (fobj (module_ran R L) M))
    (module_limit (fobj (module_ran R L) N)) t).
Defined.

Lemma module_ran_limit_iso_coordinate (R : pzRingType) {C D : category}
    (L : functor C D) (M : module_diagram R C) (x : C) :
    compose (iso_hom (module_ran_limit_iso R L M))
      (cone_leg (limit_cone (module_limit M)) x) =
    compose (cone_leg (limit_cone (module_limit (fobj (module_ran R L) M))) (fobj L x))
      (cone_leg (limit_cone (module_limit
        (functor_comp (structured_projection L (fobj L x)) M)))
        (structured_identity_point L x)).
Proof.
  exact (@right_kan_limit_iso_coordinate C D (module_category R) L M
    (fun d => module_limit (functor_comp (structured_projection L d) M))
    (module_limit M) (module_limit (fobj (module_ran R L) M)) x).
Qed.
