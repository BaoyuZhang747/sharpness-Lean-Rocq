(** Genuine derived limits are invariant under a strict category
    isomorphism, naturally in every coefficient diagram. *)
From mathcomp Require Import ssralg.
From DiazPark Require Import Category CategoryExtensionality CategoryIsomorphism
  CategoryIsomorphismAdjunction CategoryModules CategoryDerivedLimits CategoryDerivedAdjunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition derived_category_iso_nat_iso (R : pzRingType) {C D : category}
    (e : category_isomorphism C D) (n : nat) :
    @isomorphism
      (functor_category (functor_category D (module_category R)) (module_category R))
      (derived_limit_functor R D n)
      (functor_comp (precomposition (module_category R) (category_iso_forward e))
        (derived_limit_functor R C n)) :=
  derived_left_adjoint_nat_iso R (category_iso_adjunction e) n.
