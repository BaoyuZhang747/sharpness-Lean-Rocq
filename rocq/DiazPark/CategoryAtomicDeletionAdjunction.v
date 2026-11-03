From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction
  CategoryModules CategoryModuleProducts CategoryAtomicDeletionCore.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ExtensionAdjunction.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.
Local Notation CP := (full_subcategory P).
Local Notation L := (full_restriction R P).
Local Notation U := (zero_extension_functor R Pup).

Definition zero_extension_unit (D : module_codiagram R C) : nat_trans D (fobj U (fobj L D)).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R) D (fobj U (fobj L D))
  (fun x => module_product_lift (fun _ : P x => module_hom_id (fobj D x))) _).
move=> y x f; apply module_hom_ext => v; apply functional_extensionality_dep => h; reflexivity.
Defined.

Definition zero_extension_counit_component (E : module_codiagram R CP) (x : CP) :
    module_hom (fobj (fobj L (fobj U E)) x) (fobj E x).
Proof.
case: x => x hx.
exact (module_product_projection (fun h : P x => fobj E (exist _ x h)) hx).
Defined.

Definition zero_extension_counit (E : module_codiagram R CP) : nat_trans (fobj L (fobj U E)) E.
Proof.
refine (@Build_nat_trans (opposite CP) (module_category R) (fobj L (fobj U E)) E
  (zero_extension_counit_component E) _).
move=> [y hy] [x hx] f; apply module_hom_ext => v.
change (module_hom_fun (fmap E (x:=exist _ y (Pup f hx)) (y:=exist _ x hx) f)
  (v (Pup f hx)) = module_hom_fun (fmap E (x:=exist _ y hy) (y:=exist _ x hx) f) (v hy)).
rewrite (Prop_irrelevance (Pup f hx) hy); reflexivity.
Defined.

Definition zero_extension_unit_natural :
  nat_trans (functor_id _) (functor_comp L U).
Proof.
refine (@Build_nat_trans _ _ (functor_id _) (functor_comp L U) zero_extension_unit _).
move=> D E u; apply nat_trans_ext => x; apply module_hom_ext => v;
  apply functional_extensionality_dep => h; reflexivity.
Defined.

Definition zero_extension_counit_natural :
  nat_trans (functor_comp U L) (functor_id _).
Proof.
refine (@Build_nat_trans _ _ (functor_comp U L) (functor_id _) zero_extension_counit _).
move=> D E u; apply nat_trans_ext; intros [x hx]; apply module_hom_ext => v; reflexivity.
Defined.

Definition zero_extension_adjunction : adjunction L U.
Proof.
refine (@Build_adjunction _ _ L U zero_extension_unit_natural zero_extension_counit_natural _ _).
- move=> D; apply nat_trans_ext; intros [x hx]; apply module_hom_ext => v; reflexivity.
- move=> E; apply nat_trans_ext => x; apply module_hom_ext => v;
    apply functional_extensionality_dep => h; reflexivity.
Defined.

Lemma zero_extension_unit_surjective (D : module_codiagram R C) x :
  forall y, exists v, module_hom_fun (component (zero_extension_unit D) x) v = y.
Proof.
move=> y; case: (pselect (P x)) => [h|h].
- exists (y h); apply functional_extensionality_dep => h'.
  change (y h = y h'); rewrite (Prop_irrelevance h h'); reflexivity.
- exists 0; apply functional_extensionality_dep => h'; exact: False_ind (h h').
Qed.

Lemma zero_extension_unit_injective_inside (D : module_codiagram R C) x :
  P x -> injective (module_hom_fun (component (zero_extension_unit D) x)).
Proof. move=> hx v w h; exact (congr1 (fun z => z hx) h). Qed.

End ExtensionAdjunction.
