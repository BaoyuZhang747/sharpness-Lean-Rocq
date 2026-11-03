(** Explicit ordinary-limit transport from the raw double-opposite singular
    convention to the covariant elementary-category convention, with coordinates. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryModuleExactness CategoryIsomorphismAdjunction CategoryNaturalIso.
From DiazParkV28 Require Import CategoryFiberRanComparison.
From DiazParkBLO Require Import BLOE3Limits.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPBLOEdgeVariance.
Section Limits.
Variable R : pzRingType.
Variable C : category.
Variable M : module_diagram R (opposite (opposite C)).

Definition coefficient := functor_comp (DPV28FiberRanComparison.to_double_opposite C) M.

Definition raw_to_covariant_limit_iso : @isomorphism (module_category R)
    (module_limit_type M) (module_limit_type coefficient) :=
  nat_iso_component (module_left_adjoint_limit_nat_iso R
    (category_iso_adjunction (DPV28FiberRanComparison.double_opposite_iso C))) M.

Theorem raw_to_covariant_component (z : module_limit_type M) (c : C) :
  module_limit_val (module_hom_fun (iso_hom raw_to_covariant_limit_iso) z) c =
  module_limit_val z c.
Proof.
exact (congr1 (fun f => module_hom_fun f z)
  (@DPBLOE3Limits.module_adjoint_limit_coordinate R C (opposite (opposite C))
    _ _ (category_iso_adjunction (DPV28FiberRanComparison.double_opposite_iso C)) M c)).
Qed.

Theorem covariant_to_raw_component (z : module_limit_type coefficient) (c : C) :
  module_limit_val (module_hom_fun (iso_inv raw_to_covariant_limit_iso) z) c =
  module_limit_val z c.
Proof.
have h := raw_to_covariant_component (module_hom_fun (iso_inv raw_to_covariant_limit_iso) z) c.
rewrite module_iso_inv_hom_apply in h; exact: esym h.
Qed.
End Limits.
End DPBLOEdgeVariance.
