From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleProducts
  CategoryInjectives ModuleDiagrams CategoryResolutionTransport
  CategoryAtomicDeletionCore CategoryAtomicDeletionAdjunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ExactExtension.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.
Local Notation CP := (full_subcategory P).
Local Notation U := (zero_extension_functor R Pup).

Lemma zero_extension_preserves_zero : diagram_functor_preserves_zero U.
Proof. move=> F G x v; reflexivity. Qed.

Lemma zero_extension_preserves_exact : diagram_functor_preserves_exact U.
Proof.
move=> F G H a b he x v.
exact (@module_product_map_exact R (P x)
  (fun h => fobj F (exist _ x h)) (fun h => fobj G (exist _ x h))
  (fun h => fobj H (exist _ x h))
  (fun h => component a (exist _ x h)) (fun h => component b (exist _ x h))
  (fun h => he (exist _ x h)) v).
Qed.

Lemma zero_extension_preserves_injections : diagram_functor_preserves_injections U.
Proof.
move=> F G a ha x.
exact (@module_product_map_injective R (P x)
  (fun h => fobj F (exist _ x h)) (fun h => fobj G (exist _ x h))
  (fun h => component a (exist _ x h)) (fun h => ha (exist _ x h))).
Qed.

Theorem zero_extension_preserves_injectives (E : module_codiagram R CP) :
  injective_object (functor_category (opposite CP) (module_category R)) E ->
  injective_object (functor_category (opposite C) (module_category R)) (zero_extension Pup E).
Proof.
apply (right_adjoint_preserves_injectives (zero_extension_adjunction R Pup)).
exact (@module_precomposition_preserves_monomorphisms R (opposite CP) (opposite C)
  (functor_op (full_inclusion P))).
Qed.

End ExactExtension.
