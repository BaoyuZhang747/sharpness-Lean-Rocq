(** All-degree, coefficient-natural comparison for the actual right Kan
    functor. Exactness is discharged by actual comma initial families. *)
From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryComma CategoryInitialFamily CategoryModuleRightKan CategoryModuleRightKanLimits
  CategoryRanResolution CategoryDerivedLimits CategoryDerivedTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition derived_ran_nat_iso (R : pzRingType) {C D : category}
    (L : functor C D) (T : forall d, initial_family (structured_category L d)) (n : nat) :
    @isomorphism
      (functor_category (functor_category C (module_category R)) (module_category R))
      (functor_comp (module_ran R L) (derived_limit_functor R D n))
      (derived_limit_functor R C n) :=
  @derived_limit_transport_nat_iso R C D (module_ran R L)
    (@module_ran_preserves_zero R C D L) (module_ran_limit_nat_iso R L)
    (@module_ran_preserves_exact_from_family R C D L T)
    (@module_ran_preserves_injections R C D L)
    (fun F => @module_ran_preserves_injectives R C D L F) n.

Arguments derived_ran_nat_iso R {C D} L T n.
