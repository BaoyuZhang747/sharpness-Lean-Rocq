From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient MackeyModuleMaps MackeyStructures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section MackeyMorphisms.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.

Record mackey_hom (M L : @mackey_module R C B) := MackeyHom {
  mackey_component : forall P, {linear mackey_value M P -> mackey_value L P};
  mackey_hom_pull : forall P Q (f : hom C P Q) x,
    mackey_component P (mackey_pull M f x) =
      mackey_pull L f (mackey_component Q x);
  mackey_hom_push : forall P Q (f : hom C P Q) x,
    mackey_component Q (mackey_push M f x) =
      mackey_push L f (mackey_component P x)
}.

End MackeyMorphisms.

(** Actual subfunctors and quotient objects for the internal full-span
    Mackey structure. The concrete fusion inclusion-form bridge is separate. *)
Section MackeySubquotients.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : @mackey_module R C B.
Variable N : mackey_subfunctor M.

Definition subfunctor_module_value (P : C) : lmodType R :=
  [the lmodType R of submodule_carrier (subfunctor_value N P)].

Definition subfunctor_module_pull P Q (f : hom C P Q) :
    {linear subfunctor_module_value Q -> subfunctor_module_value P} :=
  submodule_map (@subfunctor_pull R C B M N P Q f).

Definition subfunctor_module_push P Q (f : hom C P Q) :
    {linear subfunctor_module_value P -> subfunctor_module_value Q} :=
  submodule_map (@subfunctor_push R C B M N P Q f).

Definition subfunctor_mackey : @mackey_module R C B.
Proof.
refine (@MackeyModule R C B subfunctor_module_value
  (@subfunctor_module_pull) (@subfunctor_module_push) _ _ _ _ _ _).
- move=> P x; apply (@submodule_val_injective R (mackey_value M P)
    (subfunctor_value N P)).
  change (mackey_pull M (identity P) (submodule_val x) = submodule_val x).
  exact: mackey_pull_id.
- move=> P x; apply (@submodule_val_injective R (mackey_value M P)
    (subfunctor_value N P)).
  change (mackey_push M (identity P) (submodule_val x) = submodule_val x).
  exact: mackey_push_id.
- move=> P Q T f g x; apply (@submodule_val_injective R (mackey_value M P)
    (subfunctor_value N P)).
  change (mackey_pull M (compose f g) (submodule_val x) =
    mackey_pull M f (mackey_pull M g (submodule_val x))).
  exact: mackey_pull_comp.
- move=> P Q T f g x; apply (@submodule_val_injective R (mackey_value M T)
    (subfunctor_value N T)).
  change (mackey_push M (compose f g) (submodule_val x) =
    mackey_push M g (mackey_push M f (submodule_val x))).
  exact: mackey_push_comp.
- move=> P Q e x; apply (@submodule_val_injective R (mackey_value M P)
    (subfunctor_value N P)).
  change (mackey_pull M (iso_hom e) (submodule_val x) =
    mackey_push M (iso_inv e) (submodule_val x)).
  exact: mackey_pull_iso.
- move=> P Q T f g x; apply (@submodule_val_injective R (mackey_value M Q)
    (subfunctor_value N Q)).
  change (mackey_pull M g (mackey_push M f (submodule_val x)) =
    submodule_inclusion (subfunctor_value N Q)
      (\sum_(i : mackey_index B f g)
        subfunctor_module_push (span_right (mackey_term B f g i))
          (subfunctor_module_pull (span_left (mackey_term B f g i)) x))).
  rewrite linear_sum.
  change (mackey_pull M g (mackey_push M f (submodule_val x)) =
    \sum_(i : mackey_index B f g)
      mackey_push M (span_right (mackey_term B f g i))
        (mackey_pull M (span_left (mackey_term B f g i)) (submodule_val x))).
  exact: mackey_formula.
Defined.

Definition quotient_module_value (P : C) : lmodType R :=
  [the lmodType R of module_quotient (subfunctor_value N P)].

Definition quotient_module_pull P Q (f : hom C P Q) :
    {linear quotient_module_value Q -> quotient_module_value P} :=
  quotient_map (@subfunctor_pull R C B M N P Q f).

Definition quotient_module_push P Q (f : hom C P Q) :
    {linear quotient_module_value P -> quotient_module_value Q} :=
  quotient_map (@subfunctor_push R C B M N P Q f).

Lemma quotient_module_pull_pi P Q (f : hom C P Q) x :
  quotient_module_pull f (quotient_pi (subfunctor_value N Q) x) =
  quotient_pi (subfunctor_value N P) (mackey_pull M f x).
Proof. exact: quotient_map_pi. Qed.

Lemma quotient_module_push_pi P Q (f : hom C P Q) x :
  quotient_module_push f (quotient_pi (subfunctor_value N P) x) =
  quotient_pi (subfunctor_value N Q) (mackey_push M f x).
Proof. exact: quotient_map_pi. Qed.

Definition quotient_mackey : @mackey_module R C B.
Proof.
refine (@MackeyModule R C B quotient_module_value
  (@quotient_module_pull) (@quotient_module_push) _ _ _ _ _ _).
- move=> P x; have [v <-] := quotient_pi_surjective (N := subfunctor_value N P) x.
  by rewrite quotient_module_pull_pi mackey_pull_id.
- move=> P x; have [v <-] := quotient_pi_surjective (N := subfunctor_value N P) x.
  by rewrite quotient_module_push_pi mackey_push_id.
- move=> P Q T f g x.
  have [v <-] := quotient_pi_surjective (N := subfunctor_value N T) x.
  by rewrite (quotient_module_pull_pi g v) !quotient_module_pull_pi mackey_pull_comp.
- move=> P Q T f g x.
  have [v <-] := quotient_pi_surjective (N := subfunctor_value N P) x.
  by rewrite (quotient_module_push_pi f v) !quotient_module_push_pi mackey_push_comp.
- move=> P Q e x.
  have [v <-] := quotient_pi_surjective (N := subfunctor_value N Q) x.
  by rewrite quotient_module_pull_pi quotient_module_push_pi mackey_pull_iso.
- move=> P Q T f g x.
  have [v <-] := quotient_pi_surjective (N := subfunctor_value N P) x.
  rewrite (quotient_module_push_pi f v) quotient_module_pull_pi.
  rewrite mackey_formula linear_sum.
  by apply: eq_bigr => i _; rewrite quotient_module_pull_pi quotient_module_push_pi.
Defined.

Definition subfunctor_inclusion : mackey_hom subfunctor_mackey M.
Proof.
refine (@MackeyHom R C B subfunctor_mackey M
  (fun P => submodule_inclusion (subfunctor_value N P)) _ _);
  by move=> P Q f x.
Defined.

Definition quotient_projection : mackey_hom M quotient_mackey.
Proof.
refine (@MackeyHom R C B M quotient_mackey
  (fun P => (quotient_pi (subfunctor_value N P) :
    {linear mackey_value M P -> quotient_module_value P})) _ _).
- move=> P Q f x; symmetry; exact: quotient_module_pull_pi.
- move=> P Q f x; symmetry; exact: quotient_module_push_pi.
Defined.

Lemma mackey_subquotient_short_exact P :
  injective (mackey_component subfunctor_inclusion P) /\
  linear_exact (mackey_component subfunctor_inclusion P)
    (mackey_component quotient_projection P) /\
  (forall y, exists x, mackey_component quotient_projection P x = y).
Proof.
split; first exact: submodule_val_injective.
split; [exact: submodule_quotient_exact | exact: quotient_pi_surjective].
Qed.

End MackeySubquotients.
