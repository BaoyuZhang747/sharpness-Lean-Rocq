(** The actual free terms induced along q:C->D. At d their basis consists
    of a composable C-string and an arrow d -> q(first vertex). *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules BarPaths BarFreeModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule.
Local Open Scope ring_scope.

Section Basis.
Variables C D : category.
Variable q : functor C D.

Definition induced_bar_basis n (d : D) : Type :=
  {s : @path C n & hom D d (fobj q (path_source s))}.

Definition induced_bar_precompose n (d e : D) (f : hom D d e)
    (s : induced_bar_basis n e) : induced_bar_basis n d :=
  existT _ (projT1 s) (compose f (projT2 s)).

Lemma induced_bar_precompose_identity n d (s : induced_bar_basis n d) :
    induced_bar_precompose (identity d) s = s.
Proof. destruct s as [s a]; unfold induced_bar_precompose; simpl.
by rewrite compose_id_left.
Qed.

Lemma induced_bar_precompose_composition n d e f (a : hom D d e) (b : hom D e f)
    (s : induced_bar_basis n f) :
    induced_bar_precompose (compose a b) s =
    induced_bar_precompose a (induced_bar_precompose b s).
Proof. destruct s as [s c]; unfold induced_bar_precompose; simpl.
by rewrite compose_assoc.
Qed.
End Basis.

Arguments induced_bar_basis {C D} q n d.
Arguments induced_bar_precompose {C D} q {n d e} f s.

Section Terms.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.

Definition induced_bar_term_obj n d : lmodType R :=
  free_module R (induced_bar_basis q n d).

Definition induced_bar_term (n : nat) : module_codiagram R D.
Proof.
refine (@Build_functor (opposite D) (module_category R)
  (induced_bar_term_obj n)
  (fun d e f => module_hom_of_linear
    (free_map R (@induced_bar_precompose C D q n e d f))) _ _).
- intro d; apply module_hom_ext; intro x.
  change (free_map R (@induced_bar_precompose C D q n d d (identity d)) x = x).
  have h : @induced_bar_precompose C D q n d d (identity d) = idfun.
    apply functional_extensionality_dep; exact: induced_bar_precompose_identity.
  by rewrite h free_map_identity.
- intros d e f a b; apply module_hom_ext; intro x.
  change (free_map R (@induced_bar_precompose C D q n f d (@compose D f e d b a)) x =
    free_map R (@induced_bar_precompose C D q n f e b)
      (free_map R (@induced_bar_precompose C D q n e d a) x)).
  rewrite -free_map_composition.
  have h : @induced_bar_precompose C D q n f d (@compose D f e d b a) =
    @induced_bar_precompose C D q n f e b \o @induced_bar_precompose C D q n e d a.
    apply functional_extensionality_dep; exact: induced_bar_precompose_composition.
  by rewrite h.
Defined.

Lemma induced_bar_term_map_basis n d e (f : hom D d e)
    (s : induced_bar_basis q n e) :
    module_hom_fun (fmap (induced_bar_term n) f) (free_basis R s) =
      free_basis R (induced_bar_precompose q f s).
Proof. exact: free_map_basis. Qed.
End Terms.

Arguments induced_bar_term_obj R {C D} q n d.
Arguments induced_bar_term R {C D} q n.
