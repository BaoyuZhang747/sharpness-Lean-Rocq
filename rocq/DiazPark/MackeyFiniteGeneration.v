From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SpanSubmodule.
Variable R : pzRingType.
Variable V : lmodType R.
Variable N : module_subspace V.
Variable X : V -> Prop.
Hypothesis hXN : forall x, X x -> N x.

Lemma span_in_submodule x : module_span X x -> forall hx : N x,
    module_span (fun y : submodule_carrier N => X (submodule_val y))
      (@submodule_in R V N x hx).
Proof.
move=> hs; elim: hs => [v hv| |v w hv ihv hw ihw|a v hv ihv] hx.
- apply: span_generator; exact hv.
- have he : @submodule_in R V N 0 hx = 0.
    apply: submodule_val_injective; exact: (esym (linear0 (submodule_inclusion N))).
  rewrite he; exact: span_zero.
- have hNv := span_least hXN hv; have hNw := span_least hXN hw.
  have he : @submodule_in R V N (v+w) hx =
      @submodule_in R V N v hNv + @submodule_in R V N w hNw.
    apply: submodule_val_injective.
    change (v+w = submodule_inclusion N
      (@submodule_in R V N v hNv + @submodule_in R V N w hNw)).
    by rewrite linearD.
  rewrite he; exact: span_add (ihv hNv) (ihw hNw).
- have hNv := span_least hXN hv.
  have he : @submodule_in R V N (a *: v) hx = a *: @submodule_in R V N v hNv.
    apply: submodule_val_injective.
    change (a *: v = submodule_inclusion N (a *: @submodule_in R V N v hNv)).
    by rewrite linearZ.
  rewrite he; exact: span_scale (ihv hNv).
Qed.

End SpanSubmodule.

Section FiniteSpanningFamily.
Variable R : pzRingType.
Variable V : lmodType R.
Variable N : module_subspace V.
Variable I : finType.
Variable v : I -> V.
Hypothesis hv : forall i, N (v i).
Hypothesis hspan : forall x, N x -> module_span (fun y => exists i, v i = y) x.

Definition finite_submodule_generator (i : I) : submodule_carrier N :=
  @submodule_in R V N (v i) (hv i).

Lemma finite_spanning_submodule : module_finitely_generated
    [the lmodType R of submodule_carrier N].
Proof.
exists [seq finite_submodule_generator i | i <- enum I] => x.
have hx := submodule_val_mem x.
have hX : forall y, (exists i, v i = y) -> N y.
  by move=> y [i <-]; exact: hv.
have hxspan := span_in_submodule (N := N) hX (hspan hx) hx.
have he : @submodule_in R V N (submodule_val x) hx = x.
  exact: submodule_val_injective.
rewrite he in hxspan.
apply: (@span_mono R [the lmodType R of submodule_carrier N]
  (fun y => exists i, v i = submodule_val y)) _ hxspan.
move=> y [i hi]; apply/mapP; exists i; first exact: mem_enum.
apply: submodule_val_injective; symmetry; exact hi.
Qed.

End FiniteSpanningFamily.

