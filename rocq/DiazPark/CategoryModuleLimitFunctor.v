(** The actual limit functor on arbitrary module diagrams and its
    coefficient-natural ordinary comparisons. No existence or comparison
    theorem is assumed: module_limit supplies the chosen universal cones. *)

From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryLimits CategoryAdjunction CategoryLimitMaps CategoryLimitFunctor
  CategoryComma CategoryModules CategoryModuleLimits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition module_limit_functor (R : pzRingType) (C : category) :
    functor (functor_category C (module_category R)) (module_category R) :=
  chosen_limit_functor (fun F => module_limit F).

Definition module_left_adjoint_limit_nat_iso (R : pzRingType)
    {C D : category} {L : functor C D} {T : functor D C} (a : adjunction L T) :
    @isomorphism
      (functor_category (functor_category D (module_category R)) (module_category R))
      (module_limit_functor R D)
      (functor_comp (precomposition (module_category R) L) (module_limit_functor R C)) :=
  left_adjoint_limit_nat_iso a (fun F => module_limit F) (fun F => module_limit F).

Definition module_contravariant_terminal_limit_nat_iso (R : pzRingType)
    {C : category} (t : terminal_object C) :
    @isomorphism
      (functor_category (functor_category (opposite C) (module_category R))
        (module_category R))
      (module_limit_functor R (opposite C))
      (evaluation_functor (opposite C) (module_category R) (terminal_point t)) :=
  chosen_limit_initial_nat_iso (fun F => module_limit F) (terminal_initial_op t).

Definition module_slice_limit_nat_iso (R : pzRingType) (C : category) (p : C) :
    @isomorphism
      (functor_category
        (functor_category (opposite (over_category C p)) (module_category R))
        (module_category R))
      (module_limit_functor R (opposite (over_category C p)))
      (evaluation_functor (opposite (over_category C p)) (module_category R)
        (over_terminal_object C p)) :=
  module_contravariant_terminal_limit_nat_iso R (@over_terminal C p).
