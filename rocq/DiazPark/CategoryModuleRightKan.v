(** Right Kan extension for arbitrary module diagrams, with the actual
    precomposition adjunction and preservation of injective diagrams. *)

From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryExtensionality CategoryLimits
  CategoryAdjunction CategoryComma CategoryStructured CategoryRightKan
  CategoryRightKanAdjunction CategoryModules CategoryModuleLimits
  CategoryNaturalIso CategoryModuleLimitFunctor CategoryInjectives ModuleDiagrams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition module_ran (R : pzRingType) {C D : category} (L : functor C D) :
    functor (functor_category C (module_category R))
      (functor_category D (module_category R)) :=
  pointwise_ran_functor L
    (fun M d => module_limit (functor_comp (structured_projection L d) M)).

Arguments module_ran R {C D} L.

Definition module_ran_adjunction (R : pzRingType) {C D : category} (L : functor C D) :
    adjunction (precomposition (module_category R) L) (module_ran R L) :=
  pointwise_ran_adjunction L
    (fun M d => module_limit (functor_comp (structured_projection L d) M)).

Arguments module_ran_adjunction R {C D} L.

(** Precomposition preserves monomorphisms by the checked pointwise
    characterization. Its constructed right adjoint therefore preserves
    injectives by the actual extension-property argument. *)
Theorem module_ran_preserves_injectives (R : pzRingType)
    {C D : category} (L : functor C D)
    (M : functor C (module_category R)) :
    injective_object (functor_category C (module_category R)) M ->
    injective_object (functor_category D (module_category R)) (fobj (module_ran R L) M).
Proof.
  apply (right_adjoint_preserves_injectives (module_ran_adjunction R L)).
  exact (@module_precomposition_preserves_monomorphisms R C D L).
Qed.

Definition module_ran_comma_iso (R : pzRingType) {C D : category}
    (L : functor C D) (M : functor C (module_category R)) (d : D) :
    @isomorphism (module_category R) (fobj (fobj (module_ran R L) M) d)
      (limit_object (module_limit (functor_comp (structured_projection L d) M))) :=
  iso_refl _.

Definition module_ran_comma_nat_iso (R : pzRingType) {C D : category}
    (L : functor C D) (d : D) :
    @isomorphism
      (functor_category (functor_category C (module_category R)) (module_category R))
      (functor_comp (module_ran R L) (evaluation_functor D (module_category R) d))
      (functor_comp (precomposition (module_category R) (structured_projection L d))
        (module_limit_functor R (structured_category L d))).
Proof.
  refine (@nat_iso_of_components (functor_category C (module_category R))
    (module_category R)
    (functor_comp (module_ran R L) (evaluation_functor D (module_category R) d))
    (functor_comp (precomposition (module_category R) (structured_projection L d))
      (module_limit_functor R (structured_category L d)))
    (fun M => iso_refl _) _).
  intros M N t.
  pose (u := ran_coefficient_map L
    (fun d => module_limit (functor_comp (structured_projection L d) M))
    (fun d => module_limit (functor_comp (structured_projection L d) N)) t d).
  exact (eq_trans (compose_id_right u) (eq_sym (compose_id_left u))).
Defined.

Lemma module_ran_unit_coordinate (R : pzRingType) {C D : category}
    (L : functor C D) (H : functor D (module_category R)) (d : D)
    (X : structured_category L d) :
    compose (component (component (adj_unit (module_ran_adjunction R L)) H) d)
      (cone_leg (limit_cone (module_limit
        (functor_comp (structured_projection L d) (functor_comp L H)))) X) =
      fmap H (structured_arrow X).
Proof.
  exact (@ran_unit_component_fac C D (module_category R) L
    (fun M d => module_limit (functor_comp (structured_projection L d) M)) H d X).
Qed.

Lemma module_ran_counit_coordinate (R : pzRingType) {C D : category}
    (L : functor C D) (M : functor C (module_category R)) (x : C) :
    component (component (adj_counit (module_ran_adjunction R L)) M) x =
      cone_leg (limit_cone (module_limit
        (functor_comp (structured_projection L (fobj L x)) M)))
        (structured_identity_point L x).
Proof. reflexivity. Qed.
