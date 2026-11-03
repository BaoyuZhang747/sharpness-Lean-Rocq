(** The explicit coinduction adjunction and preservation of injectivity. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModules ModuleInjectives ModuleCoinduced.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation "M ^z" := (zmodule M) : type_scope.

Section Coinduction.
Variable R : pzRingType.
Variable J : lmodType int.

Definition coinduced_lift_value (U : lmodType R)
    (h : module_hom [the lmodType int of U^z] J) (x : U) : coinduced R J.
Proof.
  exists (fun s : R => h (s *: x)). intros s t.
  by rewrite scalerBl module_hom_sub.
Defined.

Definition coinduced_lift (U : lmodType R)
    (h : module_hom [the lmodType int of U^z] J) :
    module_hom U (coinduced_module R J).
Proof.
  exists (coinduced_lift_value h). intros a x y.
  apply coinduced_ext. intro s.
  change (h (s *: (a *: x + y)) = h ((s*a) *: x) + h (s *: y)).
  by rewrite scalerDr scalerA module_hom_add.
Defined.

Definition coinduced_evaluate (U : lmodType R)
    (f : module_hom U (coinduced_module R J)) :
    module_hom [the lmodType int of U^z] J.
Proof.
  refine (@integer_hom_of_additive [the lmodType int of U^z] J
    (fun x => f x 1) _).
  intros x y. exact (f_equal (fun k : coinduced_module R J => k 1)
    (module_hom_sub f x y)).
Defined.

Lemma coinduced_evaluate_lift (U : lmodType R)
    (h : module_hom [the lmodType int of U^z] J) :
    coinduced_evaluate (coinduced_lift h) = h.
Proof.
  apply module_hom_ext. intro x. cbn. by rewrite scale1r.
Qed.

Lemma coinduced_lift_evaluate (U : lmodType R)
    (f : module_hom U (coinduced_module R J)) :
    coinduced_lift (coinduced_evaluate f) = f.
Proof.
  apply module_hom_ext. intro x. apply coinduced_ext. intro s.
  change (f (s *: x) 1 = f x s).
  by rewrite module_hom_scale coinduced_scale_at mul1r.
Qed.

Theorem coinduced_injective : module_injective J ->
    module_injective (coinduced_module R J).
Proof.
  intros hJ U V m hm f.
  pose (mz := @integer_hom_of_additive [the lmodType int of U^z]
    [the lmodType int of V^z] m (module_hom_sub m)).
  destruct (hJ [the lmodType int of U^z] [the lmodType int of V^z]
    mz hm (coinduced_evaluate f)) as [h hh].
  exists (coinduced_lift h). intro x. apply coinduced_ext. intro s.
  change (h (s *: m x) = f x s).
  rewrite -module_hom_scale. transitivity (coinduced_evaluate f (s *: x)).
  - exact (hh (s *: x)).
  - change (f (s *: x) 1 = f x s).
    by rewrite module_hom_scale coinduced_scale_at mul1r.
Qed.

Lemma coinduced_lift_injective (U : lmodType R)
    (h : module_hom [the lmodType int of U^z] J) :
    injective h -> injective (coinduced_lift h).
Proof.
  intros hh x y e. apply hh.
  have he := f_equal (fun k : coinduced_module R J => k 1) e.
  change (h (1 *: x) = h (1 *: y)) in he.
  by rewrite !scale1r in he.
Qed.

End Coinduction.
