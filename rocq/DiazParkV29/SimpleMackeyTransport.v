From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleExactness ModuleInfrastructure MackeyStructures MackeySubquotients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Transport of both halves of a full Mackey functor through specified
    pointwise linear isomorphisms.  All structure relations are proved;
    naturality is a theorem on the actual component maps. *)
Module DPSimpleMackeyTransport.
Record mackey_isomorphism (R : comPzRingType) (C : category) (B : mackey_shape C)
    (M N : @mackey_module R C B) := MackeyIsomorphism {
  mackey_iso_forward : mackey_hom M N;
  mackey_iso_backward : mackey_hom N M;
  mackey_iso_retract : forall P (x : mackey_value M P),
    mackey_component mackey_iso_backward P (mackey_component mackey_iso_forward P x) = x;
  mackey_iso_section : forall P (x : mackey_value N P),
    mackey_component mackey_iso_forward P (mackey_component mackey_iso_backward P x) = x
}.
Section Transport.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : @mackey_module R C B.
Variable V : C -> lmodType R.
Variable e : forall P, @isomorphism (module_category R) (mackey_value M P) (V P).
Let toV P := module_hom_to_linear (iso_hom (e P)).
Let fromV P := module_hom_to_linear (iso_inv (e P)).

Definition transported_pull_fun P Q (f : hom C P Q) (x : V Q) :=
  toV P (mackey_pull M f (fromV Q x)).
Definition transported_push_fun P Q (f : hom C P Q) (x : V P) :=
  toV Q (mackey_push M f (fromV P x)).
Lemma transported_pull_linear P Q (f : hom C P Q) : linear (transported_pull_fun f).
Proof. by move=> a x y; rewrite /transported_pull_fun !linearP. Qed.
Lemma transported_push_linear P Q (f : hom C P Q) : linear (transported_push_fun f).
Proof. by move=> a x y; rewrite /transported_push_fun !linearP. Qed.
Definition transported_pull P Q (f : hom C P Q) : {linear V Q -> V P} :=
  module_hom_to_linear (exist _ (transported_pull_fun f) (transported_pull_linear f)).
Definition transported_push P Q (f : hom C P Q) : {linear V P -> V Q} :=
  module_hom_to_linear (exist _ (transported_push_fun f) (transported_push_linear f)).

Lemma to_from P x : toV P (fromV P x) = x.
Proof. exact: module_iso_inv_hom_apply. Qed.
Lemma from_to P x : fromV P (toV P x) = x.
Proof. exact: module_iso_hom_inv_apply. Qed.

Definition transported_mackey : @mackey_module R C B.
Proof.
refine (@MackeyModule R C B V
  (@transported_pull) (@transported_push) _ _ _ _ _ _).
- move=> P x; change (transported_pull_fun (identity P) x = x).
  by rewrite /transported_pull_fun mackey_pull_id to_from.
- move=> P x; change (transported_push_fun (identity P) x = x).
  by rewrite /transported_push_fun mackey_push_id to_from.
- move=> P Q T f g x.
  change (transported_pull_fun (compose f g) x = transported_pull_fun f (transported_pull_fun g x)).
  by rewrite /transported_pull_fun from_to mackey_pull_comp.
- move=> P Q T f g x.
  change (transported_push_fun (compose f g) x = transported_push_fun g (transported_push_fun f x)).
  by rewrite /transported_push_fun from_to mackey_push_comp.
- move=> P Q d x.
  change (transported_pull_fun (iso_hom d) x = transported_push_fun (iso_inv d) x).
  by rewrite /transported_pull_fun /transported_push_fun mackey_pull_iso.
- move=> P Q T f g x.
  change (transported_pull_fun g (transported_push_fun f x) =
    \sum_(i : mackey_index B f g) transported_push_fun (span_right (mackey_term B f g i))
      (transported_pull_fun (span_left (mackey_term B f g i)) x)).
  rewrite /transported_pull_fun /transported_push_fun from_to mackey_formula linear_sum.
  apply: eq_bigr=> i _; by rewrite from_to.
Defined.

Definition to_transported : mackey_hom M transported_mackey.
Proof.
refine (@MackeyHom R C B M transported_mackey toV _ _).
- move=> P Q f x; change (toV P (mackey_pull M f x) = toV P (mackey_pull M f (fromV Q (toV Q x)))).
  by rewrite from_to.
- move=> P Q f x; change (toV Q (mackey_push M f x) = toV Q (mackey_push M f (fromV P (toV P x)))).
  by rewrite from_to.
Defined.
Definition from_transported : mackey_hom transported_mackey M.
Proof.
refine (@MackeyHom R C B transported_mackey M fromV _ _).
- move=> P Q f x; change (fromV P (toV P (mackey_pull M f (fromV Q x))) = mackey_pull M f (fromV Q x)).
  by rewrite from_to.
- move=> P Q f x; change (fromV Q (toV Q (mackey_push M f (fromV P x))) = mackey_push M f (fromV P x)).
  by rewrite from_to.
Defined.

Definition transported_isomorphism : mackey_isomorphism M transported_mackey.
Proof.
refine (@MackeyIsomorphism R C B M transported_mackey to_transported from_transported _ _).
- move=> P x; exact: from_to.
- move=> P x; exact: to_from.
Defined.

Theorem transported_simple (simpleM : mackey_simple M) : mackey_simple transported_mackey.
Proof.
split.
- have [P [x hx]] := simpleM.1; exists P, (toV P x)=> hz.
  apply: hx; rewrite -(@from_to P x) hz; exact: linear0.
- move=> N.
  pose W P := linear_preimage (toV P) (subfunctor_value N P).
  have wp : forall P Q (f : hom C P Q) x, W Q x -> W P (mackey_pull M f x).
    move=> P Q f x hx.
    have hn := @subfunctor_pull R C B transported_mackey N P Q f (toV Q x) hx.
    change (subfunctor_value N P (toV P (mackey_pull M f (fromV Q (toV Q x))))) in hn.
    by rewrite from_to in hn.
  have wt : forall P Q (f : hom C P Q) x, W P x -> W Q (mackey_push M f x).
    move=> P Q f x hx.
    have hn := @subfunctor_push R C B transported_mackey N P Q f (toV P x) hx.
    change (subfunctor_value N Q (toV Q (mackey_push M f (fromV P (toV P x))))) in hn.
    by rewrite from_to in hn.
  pose NN := @MackeySubfunctor R C B M W wp wt.
  case: (simpleM.2 NN)=> h.
  * left=> P x hx.
    have hn : W P (fromV P x) by rewrite /W /linear_preimage /= to_from.
    have hz := h P (fromV P x) hn.
    rewrite -(@to_from P x) hz; exact: linear0.
  * right=> P x; have hn := h P (fromV P x).
    change (subfunctor_value N P (toV P (fromV P x))) in hn.
    by rewrite to_from in hn.
Qed.
End Transport.
End DPSimpleMackeyTransport.
