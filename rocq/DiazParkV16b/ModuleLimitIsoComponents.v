(** Literal component formula for the actual module-limit functor on a natural isomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module DPModuleLimitIsoComponents.
Section Limit.
Variable R:pzRingType.
Variable C:category.
Variables F G:functor C (module_category R).
Variable e:@isomorphism (functor_category C (module_category R)) F G.
Definition limit_iso := functor_iso (module_limit_functor R C) e.
Theorem limit_iso_component (x:module_limit_type F) c :
 module_limit_val (module_hom_fun (iso_hom limit_iso) x) c =
 module_hom_fun (component (iso_hom e) c) (module_limit_val x c).
Proof. reflexivity. Qed.
End Limit.
End DPModuleLimitIsoComponents.
