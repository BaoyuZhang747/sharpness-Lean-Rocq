From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient MackeyModuleMaps ModuleFiniteDimensional ModuleNoetherian.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section NoetherianFiniteSpans.
Variable R : pzRingType.
Variable V : lmodType R.
Variable v : V.
Variable s : seq V.
Let N := span_subspace (fun x => x \in s).
Let P := span_subspace (fun x => x \in v :: s).

Definition span_adjoin_fun (z : (R^o * submodule_carrier N)%type) : submodule_carrier P.
Proof.
refine (@submodule_in R V P ((z.1 : R) *: v + submodule_val z.2) _).
apply: span_add.
- apply: span_scale; apply: span_generator; by rewrite in_cons eqxx.
- exact: (@span_tail R V v s _ (submodule_val_mem z.2)).
Defined.

Lemma span_adjoin_linear : linear span_adjoin_fun.
Proof.
move=> a [b x] [c y]; apply: submodule_val_injective.
change ((a*(b : R)+(c : R)) *: v + submodule_inclusion N (a *: x + y) =
  submodule_inclusion P (a *: span_adjoin_fun (b,x) + span_adjoin_fun (c,y))).
rewrite !linearP /=.
change ((a*(b : R)+(c : R)) *: v + (a *: submodule_val x + submodule_val y) =
  a *: ((b : R) *: v + submodule_val x) + ((c : R) *: v + submodule_val y)).
by rewrite scalerDl scalerDr scalerA addrACA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R
  [the lmodType R of (R^o * submodule_carrier N)%type]
  [the lmodType R of submodule_carrier P] _ span_adjoin_fun span_adjoin_linear.

Lemma span_adjoin_surjective : forall x, exists z, span_adjoin_fun z = x.
Proof.
move=> x; have [a [y [hy he]]] := span_cons_decomposition (submodule_val_mem x).
exists (a, @submodule_in R V N y hy).
apply: submodule_val_injective; exact he.
Qed.

End NoetherianFiniteSpans.

Section FiniteGenerationNoetherian.
Variable R : pzRingType.
Hypothesis ring_noetherian : module_noetherian [the lmodType R of R^o].

Lemma finite_span_noetherian (V : lmodType R) (s : seq V) :
    module_noetherian [the lmodType R of submodule_carrier
      (span_subspace (fun x => x \in s))].
Proof.
elim: s => [|v s IH].
- apply: module_noetherian_zero=> x.
  apply: submodule_val_injective.
  change (submodule_val x = submodule_inclusion
    (span_subspace (fun z : V => z \in [::])) 0).
  rewrite linear0.
  have hx := submodule_val_mem x.
  have hz : subspace_zero_space V (submodule_val x).
    apply: (@span_least R V _ (subspace_zero_space V)) hx.
    by move=> y; rewrite in_nil.
  exact hz.
- apply: (@module_noetherian_surjective R _ _
    (@span_adjoin_fun R V v s : {linear _ -> _})).
  + exact: module_noetherian_product ring_noetherian IH.
  + exact: span_adjoin_surjective.
Qed.

Theorem finitely_generated_noetherian (V : lmodType R) :
    module_finitely_generated V -> module_noetherian V.
Proof.
move=> [s hs].
pose N := span_subspace (fun x => x \in s).
apply: (@module_noetherian_surjective R _ _ (submodule_inclusion N)).
- exact: finite_span_noetherian.
- move=> x; exists (@submodule_in R V N x (hs x)); by [].
Qed.

End FiniteGenerationNoetherian.

Section PrincipalIdeals.
Variable R : comPzRingType.
Hypothesis principal_ideals : forall I : module_subspace [the lmodType R of R^o],
  exists a : R, I a /\ forall x, I x -> exists c : R, c*a = x.

Theorem principal_ideals_noetherian : module_noetherian [the lmodType R of R^o].
Proof.
move=> N; have [a [ha hN]] := principal_ideals N.
pose v := @submodule_in R [the lmodType R of R^o] N a ha.
exists [:: v] => x.
have [c hc] := hN _ (submodule_val_mem x).
have he : x = (c : R) *: v.
  apply: submodule_val_injective.
  change (submodule_val x = submodule_inclusion N ((c : R) *: v)).
  rewrite linearZ; exact: esym hc.
rewrite he; apply: span_scale; apply: span_generator; by rewrite in_cons eqxx.
Qed.

End PrincipalIdeals.

Section FiniteQuotient.
Variable R : pzRingType.
Variable V : lmodType R.

Lemma finitely_generated_quotient (N : module_subspace V) :
    module_finitely_generated V ->
    module_finitely_generated [the lmodType R of module_quotient N].
Proof.
move=> hV; apply: (@finitely_generated_surjective_image R _ _ (quotient_pi N)) hV.
exact: quotient_pi_surjective.
Qed.

End FiniteQuotient.



