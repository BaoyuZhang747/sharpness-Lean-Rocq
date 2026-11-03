From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import ModuleInfrastructure ModuleFiniteDimensional.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The principal-ideal form of Nakayama, proved by eliminating generators.
    The inverse-witness hypothesis permits the zero ring as well. *)
Section PrincipalNakayama.
Variable R : comPzRingType.
Variable V : lmodType R.
Variable r : R.
Hypothesis radical_r : forall a : R, exists b : R, b * (1 - r*a) = 1.
Hypothesis scalar_surjective : forall x : V, exists y : V, r *: y = x.

Lemma nakayama_remove_generator v s :
    (forall x : V, module_span (fun z => z \in v :: s) x) ->
    module_span (fun z => z \in s) v.
Proof.
move=> hs; have [x hx] := scalar_surjective v.
have [a [y [hy ex]]] := span_cons_decomposition (hs x).
have ev : (r*a) *: v + r *: y = v.
  by rewrite -scalerA -scalerDr ex.
have eu : (1-r*a) *: v = r *: y.
  have he := congr1 (fun z : V => z - (r*a) *: v) ev.
  rewrite addrAC subrr add0r in he.
  by rewrite scalerBl scale1r -he.
have [b hb] := radical_r a.
have eb : v = b *: (r *: y).
  by rewrite -eu scalerA hb scale1r.
rewrite eb; apply: span_scale; apply: span_scale; exact hy.
Qed.

Theorem finitely_generated_scalar_surjective_zero :
    module_finitely_generated V -> forall x : V, x = 0.
Proof.
move=> [s hs]; elim: s hs => [|v s IH] hs.
- move=> x; have hx := hs x.
  have hz : subspace_zero_space V x.
    apply: (@span_least R V _ (subspace_zero_space V)) hx.
    by move=> y; rewrite in_nil.
  exact hz.
- apply: IH => x.
  apply: span_cons_redundant (hs x).
  exact: nakayama_remove_generator hs.
Qed.

End PrincipalNakayama.


