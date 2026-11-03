(** Transposition through the constructed pointwise module right Kan
    adjunction, with its literal value at every structured-comma object. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryAdjunction CategoryComma CategoryStructured
  CategoryLimits CategoryRightKan CategoryRightKanAdjunction CategoryModules
  CategoryModuleLimits CategoryModuleRightKan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryModuleRanTranspose.
Section Transpose.
Variable R : pzRingType.
Variables C D : category.
Variable r : functor C D.
Variable H : module_diagram R D.
Variable B : module_diagram R C.
Variable t : nat_trans (functor_comp r H) B.

Definition transpose : nat_trans H (fobj (module_ran R r) B) :=
  nat_comp (component (adj_unit (module_ran_adjunction R r)) H)
    (fmap (module_ran R r) t).

Theorem transpose_coordinate (d : D) (X : structured_category r d) :
    module_hom_comp (component transpose d)
      (module_limit_projection (functor_comp (structured_projection r d) B) X) =
    module_hom_comp (fmap H (structured_arrow X)) (component t (structured_source X)).
Proof.
change (compose
  (compose (component (component (adj_unit (module_ran_adjunction R r)) H) d)
    (ran_coefficient_map r
      (fun d => module_limit (functor_comp (structured_projection r d) (functor_comp r H)))
      (fun d => module_limit (functor_comp (structured_projection r d) B)) t d))
  (cone_leg (limit_cone (module_limit (functor_comp (structured_projection r d) B))) X) =
  compose (fmap H (structured_arrow X)) (component t (structured_source X))).
rewrite compose_assoc ran_coefficient_map_fac -compose_assoc module_ran_unit_coordinate.
reflexivity.
Qed.

Theorem transpose_identity_coordinate (x : C) :
    module_hom_comp (component transpose (fobj r x))
      (module_limit_projection (functor_comp (structured_projection r (fobj r x)) B)
        (structured_identity_point r x)) = component t x.
Proof.
rewrite transpose_coordinate.
change (compose (fmap H (identity (fobj r x))) (component t x) = component t x).
rewrite fmap_id compose_id_left; reflexivity.
Qed.
End Transpose.
End DPCategoryModuleRanTranspose.
