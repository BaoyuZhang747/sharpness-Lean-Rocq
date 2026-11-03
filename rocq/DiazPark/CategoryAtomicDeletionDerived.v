(** Actual all-degree derived-limit comparison for extension by zero. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryModules
  CategoryDerivedLimits CategoryDerivedTransport CategoryAtomicDeletionCore
  CategoryAtomicDeletionAdjunction CategoryAtomicDeletionExact CategoryAtomicDeletionLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DerivedExtension.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.

Definition zero_extension_derived_natural_iso (n : nat) : @isomorphism
    (functor_category
      (functor_category (opposite (full_subcategory P)) (module_category R)) (module_category R))
    (functor_comp (zero_extension_functor R Pup) (derived_limit_functor R (opposite C) n))
    (derived_limit_functor R (opposite (full_subcategory P)) n) :=
  @derived_limit_transport_nat_iso R (opposite (full_subcategory P)) (opposite C)
    (zero_extension_functor R Pup) (@zero_extension_preserves_zero R C P Pup)
    (zero_extension_limit_natural_iso R Pup) (@zero_extension_preserves_exact R C P Pup)
    (@zero_extension_preserves_injections R C P Pup) (@zero_extension_preserves_injectives R C P Pup) n.

Definition zero_extension_derived_iso (E : module_codiagram R (full_subcategory P)) n :
    @isomorphism (module_category R) (derived_limit R (zero_extension Pup E) n)
      (derived_limit R E n) := nat_iso_component (zero_extension_derived_natural_iso n) E.

End DerivedExtension.
