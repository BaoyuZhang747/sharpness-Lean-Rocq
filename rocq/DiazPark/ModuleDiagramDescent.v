(** Descent through an objectwise surjective natural map. Choices of element
    preimages are made only in constructing the function: its linearity,
    naturality and uniqueness are all proved from the kernel condition. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  ModuleDiagrams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Descent.
Variable R : pzRingType.
Variable C : category.
Variables F G H : module_diagram R C.
Variable q : nat_trans F G.
Variable t : nat_trans F H.
Hypothesis qs : forall x (v : fobj G x), exists u : fobj F x,
  module_hom_fun (component q x) u = v.
Hypothesis tk : forall x (u : fobj F x), module_hom_fun (component q x) u = 0 ->
  module_hom_fun (component t x) u = 0.

Arguments qs x v : clear implicits.
Arguments tk x u _ : clear implicits.

Lemma diagram_descent_compatible x (u v : fobj F x) :
    module_hom_fun (component q x) u = module_hom_fun (component q x) v ->
    module_hom_fun (component t x) u = module_hom_fun (component t x) v.
Proof.
  intro e. apply/eqP. rewrite -subr_eq0. apply/eqP.
  rewrite -module_hom_sub. apply tk. by rewrite module_hom_sub e subrr.
Qed.

Definition diagram_descent_fun (x : C) (v : fobj G x) : fobj H x :=
  module_hom_fun (component t x)
    (proj1_sig (constructive_indefinite_description (qs x v))).

Arguments diagram_descent_fun x v : clear implicits.

Lemma diagram_descent_factor x (u : fobj F x) :
    diagram_descent_fun x (module_hom_fun (component q x) u) =
    module_hom_fun (component t x) u.
Proof.
  apply diagram_descent_compatible.
  exact (proj2_sig (constructive_indefinite_description
    (qs x (module_hom_fun (component q x) u)))).
Qed.

Lemma diagram_descent_linear x : linear (diagram_descent_fun x).
Proof.
  intros a u v. destruct (qs x u) as [u0 <-]. destruct (qs x v) as [v0 <-].
  transitivity (diagram_descent_fun x (module_hom_fun (component q x) (a *: u0 + v0))).
  - apply f_equal. symmetry. exact (module_hom_linear (component q x) a u0 v0).
  - transitivity (module_hom_fun (component t x) (a *: u0 + v0)).
    + apply diagram_descent_factor.
    + transitivity (a *: module_hom_fun (component t x) u0 +
        module_hom_fun (component t x) v0).
      * apply module_hom_linear.
      * symmetry. apply f_equal2.
        -- apply f_equal. apply diagram_descent_factor.
        -- apply diagram_descent_factor.
Qed.

Definition diagram_descent_component (x : C) : module_hom (fobj G x) (fobj H x) :=
  exist _ (diagram_descent_fun x) (@diagram_descent_linear x).

Definition diagram_descent : nat_trans G H.
Proof.
  refine (@Build_nat_trans C (module_category R) G H diagram_descent_component _).
  intros x y f. apply module_hom_ext. intro v. destruct (qs x v) as [u <-].
  change (diagram_descent_fun y
    (module_hom_fun (fmap G f) (module_hom_fun (component q x) u)) =
    module_hom_fun (fmap H f)
      (diagram_descent_fun x (module_hom_fun (component q x) u))).
  pose proof (f_equal (fun k : module_hom (fobj F x) (fobj G y) => k u)
    (naturality q f)) as hq.
  change (module_hom_fun (component q y) (module_hom_fun (fmap F f) u) =
    module_hom_fun (fmap G f) (module_hom_fun (component q x) u)) in hq.
  rewrite <- hq. rewrite !diagram_descent_factor.
  exact (f_equal (fun k : module_hom (fobj F x) (fobj H y) => k u)
    (naturality t f)).
Defined.

Lemma diagram_descent_fac : nat_comp q diagram_descent = t.
Proof.
  apply nat_trans_ext. intro x. apply module_hom_ext. intro u.
  apply diagram_descent_factor.
Qed.

Lemma diagram_descent_unique (s : nat_trans G H) :
    nat_comp q s = t -> s = diagram_descent.
Proof.
  intro e. apply nat_trans_ext. intro x. apply module_hom_ext. intro v.
  destruct (qs x v) as [u <-].
  change (module_hom_fun (component s x) (module_hom_fun (component q x) u) =
    diagram_descent_fun x (module_hom_fun (component q x) u)).
  rewrite diagram_descent_factor.
  exact (f_equal (fun k : nat_trans F H => module_hom_fun (component k x) u) e).
Qed.

End Descent.
