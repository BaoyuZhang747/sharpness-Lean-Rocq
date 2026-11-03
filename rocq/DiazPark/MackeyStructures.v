From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category ModuleInfrastructure.

(** Paired arbitrary-module functors with the full span Mackey formula.
    The concrete fusion constructor must supply the actual double-coset
    spans; no generation, classification, or vanishing result is a field. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Record mackey_span (C : category) (P Q : C) := MackeySpan {
  span_apex : C;
  span_left : hom C span_apex P;
  span_right : hom C span_apex Q
}.

Arguments span_apex {C P Q} _.
Arguments span_left {C P Q} _.
Arguments span_right {C P Q} _.

Record mackey_shape (C : category) := MackeyShape {
  mackey_index : forall P Q T : C, hom C P T -> hom C Q T -> finType;
  mackey_term : forall P Q T (f : hom C P T) (g : hom C Q T),
    mackey_index f g -> mackey_span P Q
}.

Arguments mackey_index {C} _ {P Q T} _ _.
Arguments mackey_term {C} _ {P Q T} _ _ _.

Section MackeyModules.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.

Record mackey_module := MackeyModule {
  mackey_value : C -> lmodType R;
  mackey_pull : forall P Q, hom C P Q ->
    {linear mackey_value Q -> mackey_value P};
  mackey_push : forall P Q, hom C P Q ->
    {linear mackey_value P -> mackey_value Q};
  mackey_pull_id : forall P x, mackey_pull (identity P) x = x;
  mackey_push_id : forall P x, mackey_push (identity P) x = x;
  mackey_pull_comp : forall P Q T (f : hom C P Q) (g : hom C Q T) x,
    mackey_pull (compose f g) x = mackey_pull f (mackey_pull g x);
  mackey_push_comp : forall P Q T (f : hom C P Q) (g : hom C Q T) x,
    mackey_push (compose f g) x = mackey_push g (mackey_push f x);
  mackey_pull_iso : forall P Q (e : isomorphism P Q) x,
    mackey_pull (iso_hom e) x = mackey_push (iso_inv e) x;
  mackey_formula : forall P Q T (f : hom C P T) (g : hom C Q T) x,
    mackey_pull g (mackey_push f x) =
      \sum_(i : mackey_index B f g)
        mackey_push (span_right (mackey_term B f g i))
          (mackey_pull (span_left (mackey_term B f g i)) x)
}.

Arguments mackey_value _ _.
Arguments mackey_pull _ {P Q} _.
Arguments mackey_push _ {P Q} _.

Variable M : mackey_module.

Record mackey_subfunctor := MackeySubfunctor {
  subfunctor_value : forall P, module_subspace (mackey_value M P);
  subfunctor_pull : forall P Q (f : hom C P Q) x,
    subfunctor_value Q x -> subfunctor_value P (mackey_pull M f x);
  subfunctor_push : forall P Q (f : hom C P Q) x,
    subfunctor_value P x -> subfunctor_value Q (mackey_push M f x)
}.

Definition mackey_nonzero := exists P, exists x : mackey_value M P, x <> 0.

Definition mackey_simple := mackey_nonzero /\ forall N : mackey_subfunctor,
  (forall P x, subfunctor_value N P x -> x = 0) \/
  (forall P x, subfunctor_value N P x).

Definition mackey_least_nonzero (rank : C -> nat) (Q : C) :=
  (exists x : mackey_value M Q, x <> 0) /\
  forall P, (rank P < rank Q)%N -> forall x : mackey_value M P, x = 0.

Lemma mackey_push_iso_cancel P Q (e : isomorphism P Q)
    (x : mackey_value M P) :
  mackey_push M (iso_inv e) (mackey_push M (iso_hom e) x) = x.
Proof.
rewrite -mackey_push_comp iso_hom_inv.
exact: mackey_push_id.
Qed.

Lemma mackey_push_iso_injective P Q (e : isomorphism P Q) :
  injective (mackey_push M (iso_hom e)).
Proof. exact: can_inj (mackey_push_iso_cancel e). Qed.

Lemma mackey_nonzero_transport P Q (e : isomorphism P Q) :
  (exists x : mackey_value M P, x <> 0) ->
  exists x : mackey_value M Q, x <> 0.
Proof.
move=> [x hx]; exists (mackey_push M (iso_hom e) x) => hz.
apply: hx; apply (@mackey_push_iso_injective P Q e).
by rewrite hz linear0.
Qed.

Definition mackey_scalar_kernel (r : R) : mackey_subfunctor.
Proof.
refine (@MackeySubfunctor (fun P => @scalar_kernel R (mackey_value M P) r)
  _ _).
- move=> P Q f x hx; exact: linear_preserves_scalar_kernel hx.
- move=> P Q f x hx; exact: linear_preserves_scalar_kernel hx.
Defined.

Definition mackey_scalar_image (r : R) : mackey_subfunctor.
Proof.
refine (@MackeySubfunctor (fun P => @scalar_image R (mackey_value M P) r)
  _ _).
- move=> P Q f x hx; exact: linear_preserves_scalar_image hx.
- move=> P Q f x hx; exact: linear_preserves_scalar_image hx.
Defined.

End MackeyModules.
