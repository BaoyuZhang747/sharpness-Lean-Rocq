(** Positive strict-fibre acyclicity gives the all-degree comparison for the
    actual right Kan extension. Degree zero is retained, not required to vanish. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryIsomorphism CategoryModules CategoryModuleExactness CategoryModuleRightKan
  CategoryFibration CategoryComma CategoryStructured
  CategoryDerivedLimits CategoryDerivedAdjunction HomologicalModuleIso.
From DiazParkV16b Require Import CategoryRanAcyclicComparisonResolution CategoryRanAcyclicComparison.
From DiazParkV28 Require Import CategoryFiberCommaAdjunction.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPV28FiberRanComparison.

Definition to_double_opposite (C : category) : functor C (opposite (opposite C)).
Proof. refine (@Build_functor C (opposite (opposite C)) (fun x => x) (fun x y f => f) _ _); reflexivity. Defined.

Definition from_double_opposite (C : category) : functor (opposite (opposite C)) C.
Proof. refine (@Build_functor (opposite (opposite C)) C (fun x => x) (fun x y f => f) _ _); reflexivity. Defined.

Definition double_opposite_iso (C : category) : category_isomorphism C (opposite (opposite C)).
Proof.
refine (@Build_category_isomorphism C (opposite (opposite C))
  (to_double_opposite C) (from_double_opposite C) _ _).
- apply (@CategoryIsomorphism.functor_extensionality C C _ _ (Logic.eq_refl _)); reflexivity.
- apply (@CategoryIsomorphism.functor_extensionality (opposite (opposite C))
    (opposite (opposite C)) _ _ (Logic.eq_refl _)); reflexivity.
Defined.

Section Fibres.
Variable R : pzRingType.
Variables C D : category.
Variable r : functor C D.
Variable hp : fibration r.
Variable M : module_diagram R C.

Lemma comma_fibre_coefficient (b : D) :
  functor_comp (DPV28FiberCommaAdjunction.fiber_comma_functor r b)
    (functor_comp (structured_projection r b) M) =
  functor_comp (fiber_inclusion r b) M.
Proof.
rewrite -functor_comp_assoc DPV28FiberCommaAdjunction.fiber_comma_projection.
reflexivity.
Qed.

Definition comma_fibre_higher_limit_iso (b : D) (s : nat) :
  @isomorphism (module_category R)
    (derived_limit R (functor_comp (structured_projection r b) M) s)
    (derived_limit R (functor_comp (fiber_inclusion r b) M) s).
Proof.
rewrite -(comma_fibre_coefficient b).
exact (nat_iso_component
  (derived_left_adjoint_nat_iso R (DPV28FiberCommaAdjunction.fiber_comma_adjunction hp b) s)
  (functor_comp (structured_projection r b) M)).
Defined.

Definition fibre_positive_acyclic : Prop :=
  forall b j (v : derived_limit R (functor_comp (fiber_inclusion r b) M) j.+1), v = 0.

Lemma comma_positive_acyclic (hM : fibre_positive_acyclic) :
  ran_comma_positive_acyclic R r M.
Proof.
move=> b j v; apply (@module_iso_hom_injective R _ _ (comma_fibre_higher_limit_iso b j.+1)).
rewrite module_hom_zero; exact: hM.
Qed.

Definition fibre_acyclic_higher_limit_iso (hM : fibre_positive_acyclic) (s : nat) :
  @isomorphism (module_category R)
    (derived_limit R (fobj (CategoryModuleRightKan.module_ran R r) M) s)
    (derived_limit R M s) :=
  ran_acyclic_higher_limit_iso R r (comma_positive_acyclic hM) s.

End Fibres.
End DPV28FiberRanComparison.
