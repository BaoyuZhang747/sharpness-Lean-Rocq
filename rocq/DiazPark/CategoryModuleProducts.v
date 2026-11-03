(** Arbitrary dependent products of MathComp modules. The index is an
    unrestricted type, and the coefficient ring may be the zero ring.
    Classical equality/choice and function extensionality are imported
    from the same explicitly audited boolp foundation as the carriers. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryModules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section DependentModuleProduct.
Variable R : pzRingType.
Variable I : Type.
Variable V : I -> lmodType R.

Definition module_product := classicType (forall i : I, V i).
HB.instance Definition _ := Choice.on module_product.

Definition module_product_zero : module_product := fun i => 0.
Definition module_product_opp (x : module_product) : module_product :=
  fun i => - x i.
Definition module_product_add (x y : module_product) : module_product :=
  fun i => x i + y i.
Definition module_product_scale (a : R) (x : module_product) : module_product :=
  fun i => a *: x i.

Lemma module_product_addA : associative module_product_add.
Proof.
  intros x y z. apply functional_extensionality_dep. intro i.
  exact (addrA (x i) (y i) (z i)).
Qed.

Lemma module_product_addC : commutative module_product_add.
Proof.
  intros x y. apply functional_extensionality_dep. intro i.
  exact (addrC (x i) (y i)).
Qed.

Lemma module_product_add0 : left_id module_product_zero module_product_add.
Proof.
  intro x. apply functional_extensionality_dep. intro i. exact (add0r (x i)).
Qed.

Lemma module_product_addN :
    left_inverse module_product_zero module_product_opp module_product_add.
Proof.
  intro x. apply functional_extensionality_dep. intro i. exact (addNr (x i)).
Qed.

HB.instance Definition _ := GRing.isZmodule.Build module_product
  module_product_addA module_product_addC module_product_add0 module_product_addN.

Lemma module_product_scaleA a b x :
    module_product_scale a (module_product_scale b x) =
      module_product_scale (a * b) x.
Proof. apply functional_extensionality_dep. intro i. exact (scalerA a b (x i)). Qed.

Lemma module_product_scale1 : left_id 1 module_product_scale.
Proof. intro x. apply functional_extensionality_dep. intro i. exact (scale1r (x i)). Qed.

Lemma module_product_scaleD : right_distributive module_product_scale +%R.
Proof.
  intros a x y. apply functional_extensionality_dep. intro i.
  exact (scalerDr a (x i) (y i)).
Qed.

Lemma module_product_scaleDl x a b :
    module_product_scale (a + b) x =
      module_product_scale a x + module_product_scale b x.
Proof.
  apply functional_extensionality_dep. intro i.
  change ((a + b) *: x i = a *: x i + b *: x i). by rewrite scalerDl.
Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R module_product
  module_product_scaleA module_product_scale1
  module_product_scaleD module_product_scaleDl.

Definition module_product_type : lmodType R := [the lmodType R of module_product].

Lemma module_product_zero_at i : (0 : module_product_type) i = 0.
Proof. reflexivity. Qed.

Lemma module_product_add_at (x y : module_product_type) i :
    (x + y) i = x i + y i.
Proof. reflexivity. Qed.

Lemma module_product_scale_at a (x : module_product_type) i :
    (a *: x) i = a *: x i.
Proof. reflexivity. Qed.

Definition module_product_projection (i : I) :
    module_hom module_product_type (V i).
Proof. exists (fun x => x i). intros a x y. reflexivity. Defined.

Definition module_product_lift (U : lmodType R)
    (f : forall i, module_hom U (V i)) : module_hom U module_product_type.
Proof.
  exists (fun x i => f i x). intros a x y.
  apply functional_extensionality_dep. intro i. apply module_hom_linear.
Defined.

Lemma module_product_lift_at (U : lmodType R)
    (f : forall i, module_hom U (V i)) (x : U) (i : I) :
    module_product_lift f x i = f i x.
Proof. reflexivity. Qed.

Lemma module_product_lift_fac (U : lmodType R)
    (f : forall i, module_hom U (V i)) (i : I) :
    module_hom_comp (module_product_lift f) (module_product_projection i) = f i.
Proof. apply module_hom_ext. intro x. reflexivity. Qed.

Lemma module_product_hom_ext (U : lmodType R)
    (f g : module_hom U module_product_type)
    (h : forall i, module_hom_comp f (module_product_projection i) =
      module_hom_comp g (module_product_projection i)) : f = g.
Proof.
  apply module_hom_ext. intro x.
  apply functional_extensionality_dep. intro i.
  exact (f_equal (fun k : module_hom U (V i) => k x) (h i)).
Qed.

Lemma module_product_lift_unique (U : lmodType R)
    (f : forall i, module_hom U (V i)) (g : module_hom U module_product_type)
    (h : forall i, module_hom_comp g (module_product_projection i) = f i) :
    g = module_product_lift f.
Proof.
  apply module_product_hom_ext. intro i.
  rewrite module_product_lift_fac. exact (h i).
Qed.

End DependentModuleProduct.

Arguments module_product {R I} V.
Arguments module_product_type {R I} V.
Arguments module_product_projection {R I} V i.
Arguments module_product_lift {R I V U} f.

Section ProductMaps.
Variable R : pzRingType.
Variable I : Type.
Variables V W X : I -> lmodType R.

Definition module_product_map (f : forall i, module_hom (V i) (W i)) :
    module_hom (module_product_type V) (module_product_type W).
Proof.
  exists (fun x i => f i (x i)). intros a x y.
  apply functional_extensionality_dep. intro i. apply module_hom_linear.
Defined.

Lemma module_product_map_at (f : forall i, module_hom (V i) (W i))
    (x : module_product_type V) i : module_product_map f x i = f i (x i).
Proof. reflexivity. Qed.

Lemma module_product_map_injective (f : forall i, module_hom (V i) (W i))
    (h : forall i, injective (f i)) : injective (module_product_map f).
Proof.
  intros x y e. apply functional_extensionality_dep. intro i.
  apply (h i). exact (f_equal (fun z : module_product_type W => z i) e).
Qed.

(** Arbitrary products preserve surjections using the explicitly imported
    classical choice principle. No finite support or finite index is used. *)
Lemma module_product_map_surjective (f : forall i, module_hom (V i) (W i))
    (h : forall i y, exists x, f i x = y) :
    forall y, exists x, module_product_map f x = y.
Proof.
  intro y.
  exists (fun i => proj1_sig (constructive_indefinite_description (h i (y i)))).
  apply functional_extensionality_dep. intro i.
  exact (proj2_sig (constructive_indefinite_description (h i (y i)))).
Qed.

End ProductMaps.

Arguments module_product_map {R I V W} f.

Section ProductExactness.
Variable R : pzRingType.
Variable I : Type.
Variables V W X : I -> lmodType R.
Variable f : forall i, module_hom (V i) (W i).
Variable g : forall i, module_hom (W i) (X i).

Lemma module_product_map_exact
    (h : forall i y, g i y = 0 <-> exists x, f i x = y)
    (y : module_product_type W) :
    module_product_map g y = 0 <-> exists x, module_product_map f x = y.
Proof.
  split.
  - intro e.
    pose (hi := fun i =>
      (proj1 (h i (y i)))
        (f_equal (fun z : module_product_type X => z i) e)).
    exists (fun i => proj1_sig (constructive_indefinite_description (hi i))).
    apply functional_extensionality_dep. intro i.
    exact (proj2_sig (constructive_indefinite_description (hi i))).
  - intros [x e]. apply functional_extensionality_dep. intro i.
    apply (proj2 (h i (y i))). exists (x i).
    exact (f_equal (fun z : module_product_type W => z i) e).
Qed.

End ProductExactness.
