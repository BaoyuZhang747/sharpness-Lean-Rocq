From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryModules
  CategoryModuleProducts CategoryModuleLimits CategoryModuleLimitFunctor
  CategoryAtomicDeletionCore ModuleInfrastructure MackeyModuleCarriers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ExtensionLimits.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.
Local Notation CP := (full_subcategory P).
Local Notation U := (zero_extension_functor R Pup).

Section Coefficient.
Variable E : module_codiagram R CP.

Definition zero_extension_limit_restrict (v : module_limit_type (zero_extension Pup E)) :
    module_limit_type E.
Proof.
refine (@submodule_in R (module_product_type (fobj E)) (module_limit_subspace E)
  (fun x : CP => match x with exist x hx => module_limit_val v x hx end) _).
move=> [y hy] [x hx] f.
have h := congr1 (fun z => z hx) (module_limit_val_compatible v f).
change (module_hom_fun (fmap E (x:=exist _ y (Pup f hx)) (y:=exist _ x hx) f)
  (module_limit_val v y (Pup f hx)) = module_limit_val v x hx) in h.
rewrite (Prop_irrelevance (Pup f hx) hy) in h; exact h.
Defined.

Definition zero_extension_limit_extend (v : module_limit_type E) :
    module_limit_type (zero_extension Pup E).
Proof.
refine (@submodule_in R (module_product_type (fobj (zero_extension Pup E)))
  (module_limit_subspace (zero_extension Pup E))
  (fun x h => module_limit_val v (exist _ x h)) _).
move=> y x f; apply functional_extensionality_dep => h.
exact (@module_limit_val_compatible R (opposite CP) E v
  (exist _ y (Pup f h)) (exist _ x h) f).
Defined.

Definition zero_extension_limit_iso : @isomorphism (module_category R)
    (module_limit_type (zero_extension Pup E)) (module_limit_type E).
Proof.
unshelve refine (@Build_isomorphism (module_category R) _ _
  (exist _ zero_extension_limit_restrict _) (exist _ zero_extension_limit_extend _) _ _).
- move=> a v w; apply module_limit_val_injective; apply functional_extensionality_dep.
  intros [x hx]; reflexivity.
- move=> a v w; apply module_limit_val_injective; apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => h; reflexivity.
- apply module_hom_ext => v; apply module_limit_val_injective.
  apply functional_extensionality_dep => x; apply functional_extensionality_dep => h; reflexivity.
- apply module_hom_ext => v; apply module_limit_val_injective.
  apply functional_extensionality_dep; intros [x hx]; reflexivity.
Defined.
End Coefficient.

Definition zero_extension_limit_natural_iso : @isomorphism
    (functor_category (functor_category (opposite CP) (module_category R)) (module_category R))
    (functor_comp U (module_limit_functor R (opposite C)))
    (module_limit_functor R (opposite CP)).
Proof.
apply: (@nat_iso_of_components _ _
  (functor_comp U (module_limit_functor R (opposite C)))
  (module_limit_functor R (opposite CP)) zero_extension_limit_iso).
move=> E F u; apply module_hom_ext => v; apply module_limit_val_injective.
apply functional_extensionality_dep; intros [x hx]; reflexivity.
Defined.

End ExtensionLimits.
