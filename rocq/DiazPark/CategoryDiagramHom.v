(** The actual module of natural transformations between arbitrary module
    diagrams over a commutative ring, including the zero ring. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  ModuleDiagrams CategoryDiagramAdditive MackeyModuleCarriers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition module_scale_hom {R : comPzRingType} {U V : lmodType R}
    (a : R) (f : module_hom U V) : module_hom U V.
Proof.
exists (fun v => a *: f v). intros b u v.
rewrite module_hom_linear scalerDr !scalerA (mulrC a b). reflexivity.
Defined.

Definition diagram_scale {R : comPzRingType} {C : category}
    {A D : module_diagram R C} (a : R) (f : nat_trans A D) : nat_trans A D.
Proof.
refine (@Build_nat_trans C (module_category R) A D
  (fun x => module_scale_hom a (component f x)) _).
intros x y u; apply module_hom_ext; intro v.
change (a *: module_hom_fun (component f y) (module_hom_fun (fmap A u) v) =
  module_hom_fun (fmap D u) (a *: module_hom_fun (component f x) v)).
rewrite module_hom_scale. apply f_equal.
exact (congr1 (fun h : module_hom (fobj A x) (fobj D y) => h v) (naturality f u)).
Defined.

Section HomModule.
Variable R : comPzRingType.
Variable C : category.
Variables A D : module_diagram R C.

Definition diagram_hom_opp (f : nat_trans A D) := diagram_sub (diagram_zero A D) f.

Definition diagram_hom_bare : @bare_module R.
Proof.
refine (@BareModule R (nat_trans A D) (diagram_zero A D) (@diagram_add R C A D)
  diagram_hom_opp (@diagram_scale R C A D) _ _ _ _ _ _ _ _).
- intros f g h; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  exact (addrA (module_hom_fun (component f x) v) (module_hom_fun (component g x) v)
    (module_hom_fun (component h x) v)).
- intros f g; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  exact (addrC (module_hom_fun (component f x) v) (module_hom_fun (component g x) v)).
- intro f; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  exact (add0r (module_hom_fun (component f x) v)).
- intro f; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  change ((0 - module_hom_fun (component f x) v) + module_hom_fun (component f x) v = 0).
  by rewrite sub0r addNr.
- intros a b f; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  exact (scalerA a b (module_hom_fun (component f x) v)).
- intro f; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  exact (scale1r (module_hom_fun (component f x) v)).
- intros a f g; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  exact (scalerDr a (module_hom_fun (component f x) v) (module_hom_fun (component g x) v)).
- intros f a b; apply nat_trans_ext; intro x; apply module_hom_ext; intro v.
  exact (scalerDl (module_hom_fun (component f x) v) a b).
Defined.

Definition diagram_hom_type : lmodType R := [the lmodType R of classical_module diagram_hom_bare].

Definition diagram_hom_at (f : diagram_hom_type) (x : C) (v : fobj A x) : fobj D x :=
  module_hom_fun (component f x) v.
Arguments diagram_hom_at f x v : clear implicits.

Lemma diagram_hom_ext (f g : diagram_hom_type) :
    (forall x v, diagram_hom_at f x v = diagram_hom_at g x v) -> f = g.
Proof. intro h; apply nat_trans_ext; intro x; apply module_hom_ext; exact (h x). Qed.

Lemma diagram_hom_at_zero x v : diagram_hom_at 0 x v = 0.
Proof. reflexivity. Qed.
Lemma diagram_hom_at_add (f g : diagram_hom_type) x v :
    diagram_hom_at (f + g) x v = diagram_hom_at f x v + diagram_hom_at g x v.
Proof. reflexivity. Qed.
Lemma diagram_hom_at_scale a (f : diagram_hom_type) x v :
    diagram_hom_at (a *: f) x v = a *: diagram_hom_at f x v.
Proof. reflexivity. Qed.
Lemma diagram_hom_at_opp (f : diagram_hom_type) x v :
    diagram_hom_at (- f) x v = - diagram_hom_at f x v.
Proof. change (0 - diagram_hom_at f x v = - diagram_hom_at f x v); exact: sub0r. Qed.

Lemma diagram_hom_at_linear x v : linear (fun f : diagram_hom_type => diagram_hom_at f x v).
Proof. intros a f g; reflexivity. Qed.

End HomModule.
Arguments diagram_hom_type {R C} A D.
Arguments diagram_hom_at {R C A D} f x v.
Arguments diagram_hom_ext {R C A D} f g h.

Section Postcompose.
Variable R : comPzRingType.
Variable C : category.
Variable A : module_diagram R C.
Variables D E : module_diagram R C.
Variable u : nat_trans D E.

Definition diagram_hom_post (f : diagram_hom_type A D) : diagram_hom_type A E := nat_comp f u.
Lemma diagram_hom_post_at f x v :
    diagram_hom_at (diagram_hom_post f) x v =
      module_hom_fun (component u x) (diagram_hom_at f x v).
Proof. reflexivity. Qed.
Lemma diagram_hom_post_linear : linear diagram_hom_post.
Proof.
intros a f g; apply diagram_hom_ext; intros x v.
change (module_hom_fun (component u x)
  (a *: diagram_hom_at f x v + diagram_hom_at g x v) =
  a *: module_hom_fun (component u x) (diagram_hom_at f x v) +
    module_hom_fun (component u x) (diagram_hom_at g x v)).
exact: module_hom_linear.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (diagram_hom_type A D) (diagram_hom_type A E) _
  diagram_hom_post diagram_hom_post_linear.
End Postcompose.
Arguments diagram_hom_post {R C} A {D E} u f.

Definition diagram_hom_functor (R : comPzRingType) (C : category) (A : module_diagram R C) :
    functor (functor_category C (module_category R)) (module_category R).
Proof.
refine (@Build_functor (functor_category C (module_category R)) (module_category R)
  (fun D => diagram_hom_type A D)
  (fun D E u => module_hom_of_linear (@diagram_hom_post R C A D E u)) _ _).
- intro D; apply module_hom_ext; intro f; apply diagram_hom_ext; intros x v; reflexivity.
- intros D E H u v; apply module_hom_ext; intro f; apply diagram_hom_ext; intros x w; reflexivity.
Defined.


