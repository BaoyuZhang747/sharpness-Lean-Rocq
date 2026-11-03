(** The induced free bar terms are actual projective module diagrams;
    their Hom term isomorphisms are natural in arbitrary coefficients. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  CategoryDiagramHom CategoryEnoughProjectives BarComplex
  HomologicalModuleIso.
From DiazParkV16b Require Import CategoryInducedBarTerms CategoryInducedBarHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectives DiazParkBarComplex DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Section Projective.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.
Variables M N : module_codiagram R D.
Variable u : nat_trans M N.
Hypothesis hu : forall d (v : fobj N d), exists w, module_hom_fun (component u d) w = v.

Theorem induced_bar_term_lift n (a : nat_trans (induced_bar_term R q n) N) :
    exists b : nat_trans (induced_bar_term R q n) M, nat_comp b u = a.
Proof.
pose c : bar_term (functor_comp (functor_op q) M) n := fun x s =>
  proj1_sig (constructive_indefinite_description
    (@hu (fobj q x) (@induced_bar_to_cochain R C D q N n a x s))).
exists (induced_bar_from_cochain q c).
apply (@induced_bar_to_cochain_injective R C D q N n).
apply functional_extensionality_dep; intro x.
apply functional_extensionality_dep; intro s.
change (module_hom_fun (component u (fobj q x))
  (@induced_bar_to_cochain R C D q M n (induced_bar_from_cochain q c) x s) =
  @induced_bar_to_cochain R C D q N n a x s).
rewrite induced_bar_cochain_inverse /c.
exact: (proj2_sig (constructive_indefinite_description
  (@hu (fobj q x) (@induced_bar_to_cochain R C D q N n a x s)))).
Qed.
End Projective.

Theorem induced_bar_term_projective (R : pzRingType) {C D : category}
    (q : functor C D) n :
    projective_object (functor_category (opposite D) (module_category R))
      (induced_bar_term R q n).
Proof.
intros M N u hu a.
exact (@induced_bar_term_lift R C D q M N u
  (@epi_pointwise_surjective R (opposite D) M N u hu) n a).
Qed.

Section LinearHom.
Variable R : comPzRingType.
Variables C D : category.
Variable q : functor C D.
Variable M : module_codiagram R D.

Definition induced_bar_hom_to_cochain n
    (a : diagram_hom_type (induced_bar_term R q n) M) :
    bar_term (functor_comp (functor_op q) M) n := induced_bar_to_cochain q a.

Lemma induced_bar_hom_to_cochain_linear n : linear (@induced_bar_hom_to_cochain n).
Proof.
intros a f g; apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s; reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R
  (diagram_hom_type (induced_bar_term R q n) M)
  (bar_term (functor_comp (functor_op q) M) n) _
  (@induced_bar_hom_to_cochain n) (@induced_bar_hom_to_cochain_linear n).

Definition induced_bar_hom_term_iso n : @isomorphism (module_category R)
    (diagram_hom_type (induced_bar_term R q n) M)
    (bar_term (functor_comp (functor_op q) M) n).
Proof.
apply (@linear_bijection_iso R _ _ (@induced_bar_hom_to_cochain n : {linear _ -> _})).
- exact: induced_bar_to_cochain_injective.
- intro a; exists (induced_bar_from_cochain q a); exact: induced_bar_cochain_inverse.
Defined.
End LinearHom.

Lemma induced_bar_hom_term_naturality (R : comPzRingType) {C D : category}
    (q : functor C D) {M N : module_codiagram R D} (u : nat_trans M N) n
    (a : diagram_hom_type (induced_bar_term R q n) M) x s :
    module_hom_fun (iso_hom (@induced_bar_hom_term_iso R C D q N n)) (nat_comp a u) x s =
    module_hom_fun (component u (fobj q x))
      (module_hom_fun (iso_hom (@induced_bar_hom_term_iso R C D q M n)) a x s).
Proof. reflexivity. Qed.
