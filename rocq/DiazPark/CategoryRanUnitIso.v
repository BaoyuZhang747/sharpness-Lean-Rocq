(** Two direct criteria for the actual right-Kan adjunction unit to be an
    isomorphism: zero values, or one component with an invertible arrow. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryAdjunction CategoryComma CategoryStructured
  CategoryModules CategoryModuleExactness CategoryModuleProducts CategoryInitialFamily
  CategoryModuleInitialFamily CategoryModuleRightKan CategoryModuleRanProduct ModuleDiagrams.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section UnitIso.
Variable R : pzRingType.
Variables C D : category.
Variable L : functor C D.
Variable d : D.
Variable T : initial_family (structured_category L d).
Variable H : module_diagram R D.
Let N := functor_comp L H.
Let V := fobj (fobj (module_ran R L) N) d.
Let E := module_ran_product_iso R L T N.
Definition ran_unit_at : module_hom (fobj H d) V :=
  component (component (adj_unit (module_ran_adjunction R L)) H) d.
Lemma ran_unit_product_coordinate i x :
    module_hom_fun (iso_hom E) (ran_unit_at x) i =
      module_hom_fun (fmap H (structured_arrow (initial_family_object T i))) x.
Proof.
  exact (congr1 (fun f : module_hom (fobj H d)
    (fobj H (fobj L (structured_source (initial_family_object T i)))) => f x)
    (@module_ran_product_unit_coordinate R C D L d T H i)).
Qed.

Lemma ran_unit_zero_target
    (zeroT : forall i (x : fobj H (fobj L (structured_source (initial_family_object T i)))), x = 0) :
    forall v : V, v = 0.
Proof.
  move=> v. apply (@module_iso_hom_injective R V _ E).
  rewrite module_hom_zero. apply functional_extensionality_dep => i.
  exact (zeroT i (module_hom_fun (iso_hom E) v i)).
Qed.

Definition ran_unit_zero_iso
    (zeroH : forall x : fobj H d, x = 0)
    (zeroT : forall i (x : fobj H (fobj L (structured_source (initial_family_object T i)))), x = 0) :
    @isomorphism (module_category R) (fobj H d) V.
Proof.
  refine (@Build_isomorphism (module_category R) (fobj H d) V ran_unit_at
    (module_zero_hom V (fobj H d)) _ _).
  - apply module_hom_ext => x. exact (esym (zeroH x)).
  - apply module_hom_ext => v.
    change (ran_unit_at 0 = v). rewrite module_hom_zero. exact (esym (ran_unit_zero_target zeroT v)).
Defined.

Variable i0 : initial_family_index T.
Hypothesis only_i0 : forall i : initial_family_index T, i = i0.
Variable e : @isomorphism D d (fobj L (structured_source (initial_family_object T i0))).
Hypothesis arrow_e : iso_hom e = structured_arrow (initial_family_object T i0).
Let He := functor_iso H e.
Definition ran_unit_singleton_inverse : module_hom V (fobj H d) :=
  module_hom_comp (iso_hom E)
    (module_hom_comp (module_product_projection _ i0) (iso_inv He)).

Definition ran_unit_singleton_iso : @isomorphism (module_category R) (fobj H d) V.
Proof.
  refine (@Build_isomorphism (module_category R) (fobj H d) V ran_unit_at
    ran_unit_singleton_inverse _ _).
  - apply module_hom_ext => x.
    change (module_hom_fun (iso_inv He)
      (module_hom_fun (iso_hom E) (ran_unit_at x) i0) = x).
    rewrite ran_unit_product_coordinate -arrow_e.
    exact (module_iso_hom_inv_apply He x).
  - apply module_hom_ext => v.
    apply (@module_iso_hom_injective R V _ E).
    apply functional_extensionality_dep => i.
    rewrite (only_i0 i).
    change (module_hom_fun (iso_hom E) (ran_unit_at (ran_unit_singleton_inverse v)) i0 =
      module_hom_fun (iso_hom E) v i0).
    rewrite ran_unit_product_coordinate -arrow_e.
    exact (module_iso_inv_hom_apply He (module_hom_fun (iso_hom E) v i0)).
Defined.
End UnitIso.
