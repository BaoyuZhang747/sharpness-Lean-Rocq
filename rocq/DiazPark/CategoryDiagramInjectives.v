(** Actual coinduced diagrams of arbitrary modules. Identity coordinates
    determine every natural map into such a diagram, and module extension
    properties produce genuine injectivity in the diagram category. *)
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleProducts CategoryInjectives ModuleInjectives ModuleDiagrams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CoinducedDiagrams.
Variable R : pzRingType.
Variable C : category.
Variable I : C -> lmodType R.

Definition coinduced_object (x : C) : lmodType R :=
  module_product_type (fun c : C =>
    module_product_type (fun _ : hom C x c => I c)).

Definition coinduced_map {x y : C} (f : hom C x y) :
    module_hom (coinduced_object x) (coinduced_object y).
Proof.
  exists (fun v c g => v c (compose f g)).
  intros a v w. reflexivity.
Defined.

Definition coinduced_diagram : module_diagram R C.
Proof.
  refine (@Build_functor C (module_category R) coinduced_object
    (fun x y f => coinduced_map f) _ _).
  - intro x. apply module_hom_ext. intro v.
    apply functional_extensionality_dep. intro c.
    apply functional_extensionality_dep. intro f.
    change (v c (compose (identity x) f) = v c f).
    rewrite compose_id_left. reflexivity.
  - intros x y z f g. apply module_hom_ext. intro v.
    apply functional_extensionality_dep. intro c.
    apply functional_extensionality_dep. intro h.
    change (v c (compose (compose f g) h) = v c (compose f (compose g h))).
    rewrite compose_assoc. reflexivity.
Defined.

Definition coinduced_identity_projection (c : C) :
    module_hom (fobj coinduced_diagram c) (I c) :=
  module_hom_comp (module_product_projection _ c)
    (module_product_projection _ (identity c)).

Definition coinduced_lift_component (F : module_diagram R C)
    (a : forall c, module_hom (fobj F c) (I c)) (x : C) :
    module_hom (fobj F x) (coinduced_object x) :=
  module_product_lift (fun c => module_product_lift (fun f : hom C x c =>
    module_hom_comp (fmap F f) (a c))).

Definition coinduced_lift (F : module_diagram R C)
    (a : forall c, module_hom (fobj F c) (I c)) :
    nat_trans F coinduced_diagram.
Proof.
  refine (@Build_nat_trans C (module_category R) F coinduced_diagram
    (coinduced_lift_component a) _).
  intros x y f. apply module_hom_ext. intro v.
  apply functional_extensionality_dep. intro c.
  apply functional_extensionality_dep. intro g.
  change (a c (module_hom_fun (fmap F g) (module_hom_fun (fmap F f) v)) =
    a c (module_hom_fun (fmap F (compose f g)) v)).
  rewrite fmap_compose. reflexivity.
Defined.

Lemma coinduced_lift_coordinate (F : module_diagram R C)
    (a : forall c, module_hom (fobj F c) (I c)) x c (f : hom C x c) v :
    module_hom_fun (component (coinduced_lift a) x) v c f =
      a c (module_hom_fun (fmap F f) v).
Proof. reflexivity. Qed.

Lemma coinduced_lift_identity (F : module_diagram R C)
    (a : forall c, module_hom (fobj F c) (I c)) c v :
    module_hom_fun (component (coinduced_lift a) c) v c (identity c) = a c v.
Proof. rewrite coinduced_lift_coordinate fmap_id. reflexivity. Qed.

Lemma coinduced_natural_coordinate (F : module_diagram R C)
    (t : nat_trans F coinduced_diagram) x c (f : hom C x c) v :
    module_hom_fun (component t x) v c f =
      module_hom_fun (component t c) (module_hom_fun (fmap F f) v) c (identity c).
Proof.
  pose proof (f_equal
    (fun k : module_hom (fobj F x) (coinduced_object c) => k v c (identity c))
    (naturality t f)) as h.
  change (module_hom_fun (component t c) (module_hom_fun (fmap F f) v) c (identity c) =
    module_hom_fun (component t x) v c (compose f (identity c))) in h.
  rewrite compose_id_right in h. symmetry. exact h.
Qed.

Lemma coinduced_hom_ext (F : module_diagram R C)
    (t s : nat_trans F coinduced_diagram)
    (h : forall c v, module_hom_fun (component t c) v c (identity c) =
      module_hom_fun (component s c) v c (identity c)) : t = s.
Proof.
  apply nat_trans_ext. intro x. apply module_hom_ext. intro v.
  apply functional_extensionality_dep. intro c.
  apply functional_extensionality_dep. intro f.
  transitivity (module_hom_fun (component t c)
    (module_hom_fun (fmap F f) v) c (identity c)).
  - exact (coinduced_natural_coordinate t f v).
  - transitivity (module_hom_fun (component s c)
      (module_hom_fun (fmap F f) v) c (identity c)).
    + apply h.
    + symmetry. exact (coinduced_natural_coordinate s f v).
Qed.

Theorem coinduced_diagram_injective (hI : forall c, module_injective (I c)) :
    injective_object (functor_category C (module_category R)) coinduced_diagram.
Proof.
  intros A B m hm t.
  pose (hc := fun c => hI c (fobj A c) (fobj B c) (component m c)
    ((proj1 (diagram_monomorphism_iff m)) hm c)
    (module_hom_comp (component t c) (coinduced_identity_projection c))).
  pose (g := fun c => proj1_sig (constructive_indefinite_description (hc c))).
  exists (coinduced_lift g). apply coinduced_hom_ext. intros c v.
  change (module_hom_fun (component (coinduced_lift g) c)
    (module_hom_fun (component m c) v) c (identity c) =
    module_hom_fun (component t c) v c (identity c)).
  rewrite coinduced_lift_identity.
  exact (proj2_sig (constructive_indefinite_description (hc c)) v).
Qed.

Lemma coinduced_lift_pointwise_injective (F : module_diagram R C)
    (a : forall c, module_hom (fobj F c) (I c))
    (ha : forall c, injective (a c)) :
    forall x, injective (module_hom_fun (component (coinduced_lift a) x)).
Proof.
  intros x v w h. apply (ha x).
  pose proof (f_equal (fun z : coinduced_object x => z x (identity x)) h) as e.
  change (module_hom_fun (component (coinduced_lift a) x) v x (identity x) =
    module_hom_fun (component (coinduced_lift a) x) w x (identity x)) in e.
  rewrite !coinduced_lift_identity in e. exact e.
Qed.

End CoinducedDiagrams.

Arguments coinduced_object {R C} I x.
Arguments coinduced_diagram {R C} I.
Arguments coinduced_lift {R C I F} a.
Arguments coinduced_diagram_injective {R C I} hI.
