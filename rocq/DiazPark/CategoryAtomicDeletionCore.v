(** Upward full subcategories and actual extension by zero of contravariant
    arbitrary-module coefficients. A product over proofs of membership is
    the original value inside the subcategory and the zero module outside. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction
  CategoryModules CategoryModuleProducts ModuleDiagrams.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FullSubcategory.
Variable C : category.
Variable P : C -> Prop.

Definition full_subcategory : category.
Proof.
refine (@Build_category {x : C | P x}
  (fun x y => hom C (proj1_sig x) (proj1_sig y))
  (fun x => identity (proj1_sig x))
  (fun x y z f g => compose f g) _ _ _).
- move=> x y f; exact: compose_id_left.
- move=> x y f; exact: compose_id_right.
- move=> w x y z f g h; exact: compose_assoc.
Defined.

Definition full_inclusion : functor full_subcategory C.
Proof.
refine (@Build_functor full_subcategory C (@proj1_sig C P)
  (fun x y f => f) _ _); reflexivity.
Defined.
End FullSubcategory.

Section Extension.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.
Local Notation CP := (full_subcategory P).
Local Notation JP := (full_inclusion P).

Definition full_restriction : functor
    (functor_category (opposite C) (module_category R))
    (functor_category (opposite CP) (module_category R)) :=
  precomposition (module_category R) (functor_op JP).

Section Coefficient.
Variable E : module_codiagram R CP.
Definition zero_extension_object (x : C) : lmodType R :=
  module_product_type (fun h : P x => fobj E (exist _ x h)).

Definition zero_extension_arrow {x y : C} (f : hom C x y) :
    module_hom (zero_extension_object y) (zero_extension_object x).
Proof.
exists (fun v h => module_hom_fun (fmap E (x:=exist _ y (Pup f h)) (y:=exist _ x h) f)
  (v (Pup f h))).
move=> a v w; apply functional_extensionality_dep => h; exact: module_hom_linear.
Defined.

Definition zero_extension : module_codiagram R C.
Proof.
refine (@Build_functor (opposite C) (module_category R) zero_extension_object
  (fun y x f => zero_extension_arrow f) _ _).
- move=> x; apply module_hom_ext => v; apply functional_extensionality_dep => h.
  change (module_hom_fun (fmap E (x:=exist _ x (Pup (identity x) h))
    (y:=exist _ x h) (identity x)) (v (Pup (identity x) h)) = v h).
  rewrite (Prop_irrelevance (Pup (identity x) h) h).
  rewrite fmap_id; reflexivity.
- move=> z y x g f; apply module_hom_ext => v; apply functional_extensionality_dep => h.
  change (module_hom_fun (fmap E (x:=exist _ z (Pup (@compose C x y z f g) h))
    (y:=exist _ x h) (@compose C x y z f g)) (v (Pup (@compose C x y z f g) h)) =
    module_hom_fun (fmap E (x:=exist _ y (Pup f h)) (y:=exist _ x h) f)
      (module_hom_fun (fmap E (x:=exist _ z (Pup g (Pup f h)))
        (y:=exist _ y (Pup f h)) g) (v (Pup g (Pup f h))))).
  rewrite (Prop_irrelevance (Pup (@compose C x y z f g) h) (Pup g (Pup f h))).
  have he := fmap_compose E (x:=exist _ z (Pup g (Pup f h)))
    (y:=exist _ y (Pup f h)) (z:=exist _ x h) g f.
  exact (congr1 (fun t => module_hom_fun t (v (Pup g (Pup f h)))) he).
Defined.

Lemma zero_extension_outside x : ~ P x -> forall v : fobj zero_extension x, v = 0.
Proof. move=> hx v; apply functional_extensionality_dep => h; exact: False_ind (hx h). Qed.

End Coefficient.

Definition zero_extension_map {E F : module_codiagram R CP} (u : nat_trans E F) :
    nat_trans (zero_extension E) (zero_extension F).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R) (zero_extension E) (zero_extension F)
  (fun x => module_product_map (fun h : P x => component u (exist _ x h))) _).
move=> y x f; apply module_hom_ext => v; apply functional_extensionality_dep => h.
exact (congr1 (fun t => module_hom_fun t (v (Pup f h)))
  (naturality u (x:=exist _ y (Pup f h)) (y:=exist _ x h) f)).
Defined.

Definition zero_extension_functor : functor
    (functor_category (opposite CP) (module_category R))
    (functor_category (opposite C) (module_category R)).
Proof.
refine (@Build_functor (functor_category (opposite CP) (module_category R))
  (functor_category (opposite C) (module_category R))
  zero_extension (fun E F u => zero_extension_map u) _ _).
- move=> E; apply nat_trans_ext => x; apply module_hom_ext => v; reflexivity.
- move=> E F G u v; apply nat_trans_ext => x; apply module_hom_ext => w; reflexivity.
Defined.

End Extension.
