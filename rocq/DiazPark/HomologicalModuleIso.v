From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DiazParkHomologicalModuleIso.
Section LinearIso.
Variable R : pzRingType.
Variables U V : lmodType R.
Variable f : {linear U -> V}.
Hypothesis fi : injective f.
Hypothesis fs : forall v, exists u, f u = v.

Definition linear_inverse (v : V) : U :=
  proj1_sig (constructive_indefinite_description (fs v)).

Lemma linear_inverse_spec v : f (linear_inverse v) = v.
Proof. exact: (proj2_sig (constructive_indefinite_description (fs v))). Qed.

Lemma linear_inverse_retract u : linear_inverse (f u) = u.
Proof. apply fi; exact: linear_inverse_spec. Qed.

Lemma linear_inverse_linear : linear linear_inverse.
Proof.
move=> a x y; apply fi.
by rewrite linear_inverse_spec linearP !linear_inverse_spec.
Qed.

Definition linear_bijection_iso : @isomorphism (module_category R) U V.
Proof.
refine (@Build_isomorphism (module_category R) U V
  (module_hom_of_linear f) (exist _ linear_inverse linear_inverse_linear) _ _).
- apply module_hom_ext => u; exact: linear_inverse_retract.
- apply module_hom_ext => v; exact: linear_inverse_spec.
Defined.

End LinearIso.

Definition module_iso_comp {R : pzRingType} {U V W : lmodType R}
    (e : @isomorphism (module_category R) U V)
    (f : @isomorphism (module_category R) V W) : @isomorphism (module_category R) U W.
Proof.
refine (@Build_isomorphism (module_category R) U W
  (module_hom_comp (iso_hom e) (iso_hom f))
  (module_hom_comp (iso_inv f) (iso_inv e)) _ _).
- apply module_hom_ext => u.
  change (module_hom_fun (iso_inv e) (module_hom_fun (iso_inv f)
    (module_hom_fun (iso_hom f) (module_hom_fun (iso_hom e) u))) = u).
  by rewrite !module_iso_hom_inv_apply.
- apply module_hom_ext => u.
  change (module_hom_fun (iso_hom f) (module_hom_fun (iso_hom e)
    (module_hom_fun (iso_inv e) (module_hom_fun (iso_inv f) u))) = u).
  by rewrite !module_iso_inv_hom_apply.
Defined.

Section QuotientIso.
Variable R : pzRingType.
Variables V W : lmodType R.
Variable N : module_subspace V.
Variable f : {linear V -> W}.
Hypothesis fk : forall x, N x <-> f x = 0.
Hypothesis fs : forall w, exists v, f v = w.

Definition quotient_iso_map : {linear module_quotient N -> W} :=
  (@quotient_lift R V N W f (fun x hx => proj1 (fk x) hx) :
    {linear module_quotient N -> W}).

Lemma quotient_iso_map_pi x : quotient_iso_map (quotient_pi N x) = f x.
Proof. exact: quotient_lift_pi. Qed.

Lemma quotient_iso_map_injective : injective quotient_iso_map.
Proof.
move=> x y h.
have [a ha] := quotient_pi_surjective x.
have [b hb] := quotient_pi_surjective y.
have hab : f a = f b.
  by rewrite -(quotient_iso_map_pi a) -(quotient_iso_map_pi b) ha hb.
rewrite -ha -hb.
apply/eqP; rewrite quotient_pi_eq; apply/subspace_predP; apply/(fk (a - b)).
by rewrite linearB hab subrr.
Qed.

Lemma quotient_iso_map_surjective : forall w, exists q, quotient_iso_map q = w.
Proof. move=> w; have [v <-] := fs w; exists (quotient_pi N v); exact: quotient_iso_map_pi. Qed.

Definition quotient_linear_iso :
    @isomorphism (module_category R) [the lmodType R of module_quotient N] W :=
  linear_bijection_iso quotient_iso_map_injective quotient_iso_map_surjective.

End QuotientIso.
End DiazParkHomologicalModuleIso.
