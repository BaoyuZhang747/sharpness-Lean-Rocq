(** Actual finite composition series for arbitrary-carrier Mackey functors.
    A series is encoded by successive simple subfunctors and their actual
    quotients.  No acyclicity or classification statement is a constructor. *)
From HB Require Import structures.
From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra boolp vector.
From DiazPark Require Import Category ModuleInfrastructure MackeyStructures
  MackeySubquotients MackeyModuleCarriers MackeyModuleMaps MackeyModuleQuotient
  ModuleFiniteDimensional ModuleFiniteSubmodules ModuleFiniteDimensionMaps
  MackeyFiniteLength.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPCompositionSeries.

Section SubfunctorComposition.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : mackey_module R B.

Definition full_subfunctor : mackey_subfunctor M.
Proof.
refine (@MackeySubfunctor R C B M (fun P => subspace_full (mackey_value M P)) _ _);
  by move=> P Q f x hx.
Defined.

Variable N : mackey_subfunctor M.
Variable J : mackey_subfunctor (subfunctor_mackey N).

Definition nested_inclusion P :
    {linear mackey_value (subfunctor_mackey J) P -> mackey_value M P} :=
  (submodule_inclusion (subfunctor_value N P) \o
    submodule_inclusion (subfunctor_value J P) : {linear _ -> _}).

Definition nested_image : mackey_subfunctor M.
Proof.
refine (@MackeySubfunctor R C B M
  (fun P => linear_image (nested_inclusion P)) _ _).
- move=> P Q f x [y <-].
  exists (mackey_pull (subfunctor_mackey J) f y); reflexivity.
- move=> P Q f x [y <-].
  exists (mackey_push (subfunctor_mackey J) f y); reflexivity.
Defined.

Lemma nested_image_le P x : subfunctor_value nested_image P x ->
    subfunctor_value N P x.
Proof. move=> [y <-]; exact: submodule_val_mem. Qed.

Definition nested_to_parent_fun P (x : mackey_value (subfunctor_mackey nested_image) P) :
    mackey_value (subfunctor_mackey N) P :=
  submodule_in (nested_image_le (submodule_val_mem x)).

Arguments nested_to_parent_fun P x : clear implicits.

Lemma nested_to_parent_linear P : linear (nested_to_parent_fun P).
Proof.
move=> a x y; apply: submodule_val_injective.
change (submodule_inclusion (subfunctor_value nested_image P) (a *: x + y) =
  submodule_inclusion (subfunctor_value N P)
    (a *: nested_to_parent_fun P x + nested_to_parent_fun P y)).
by rewrite !linearP.
Qed.

HB.instance Definition _ P := GRing.isLinear.Build R _ _ _
  (nested_to_parent_fun P) (@nested_to_parent_linear P).

Definition nested_to_parent P :
    {linear mackey_value (subfunctor_mackey nested_image) P ->
      mackey_value (subfunctor_mackey N) P} := nested_to_parent_fun P.

Arguments nested_to_parent P : clear implicits.

Lemma nested_to_parent_injective P : injective (nested_to_parent P).
Proof.
move=> x y he; apply: submodule_val_injective.
exact (congr1 (@submodule_val R (mackey_value M P) (subfunctor_value N P)) he).
Qed.

Lemma nested_to_parent_in_J P x :
    subfunctor_value J P (nested_to_parent P x).
Proof.
have [y hy] := submodule_val_mem x.
have he : submodule_val y = nested_to_parent P x.
  apply: submodule_val_injective; exact: hy.
rewrite -he; exact: submodule_val_mem.
Qed.

Lemma nested_image_nonzero : mackey_nonzero (subfunctor_mackey J) ->
    mackey_nonzero (subfunctor_mackey nested_image).
Proof.
move=> [P [x hx]].
have hm : subfunctor_value nested_image P (nested_inclusion P x).
  by exists x.
exists P, (submodule_in hm) => hz; apply: hx.
apply: submodule_val_injective; apply: submodule_val_injective.
have he := congr1 (@submodule_val R (mackey_value M P)
  (subfunctor_value nested_image P)) hz.
change (nested_inclusion P x = submodule_inclusion (subfunctor_value nested_image P) 0) in he.
by rewrite linear0 in he.
Qed.

End SubfunctorComposition.

Section FiniteSimpleSubobject.
Variable K : fieldType.
Variable C : category.
Variable B : mackey_shape C.
Variable I : finType.
Variable object_at : I -> C.
Hypothesis objects_cover : forall P, exists i, object_at i = P.
Variable M : mackey_module K B.
Variable hM : mackey_finite_values M.

Definition subfunctor_dimension (N : mackey_subfunctor M) :=
  mackey_total_dimension object_at (subfunctor_finite_values hM N).

Lemma nested_proper_dimension_lt (N : mackey_subfunctor M)
    (J : mackey_subfunctor (subfunctor_mackey N)) :
    (exists P, exists x, ~ subfunctor_value J P x) ->
    (subfunctor_dimension (nested_image J) < subfunctor_dimension N)%N.
Proof.
move=> [P [x hx]]; have [i hi] := objects_cover P.
have hle Q :
    (dim (chosen_finite_model (subfunctor_finite_values hM (nested_image J) Q)) <=
     dim (chosen_finite_model (subfunctor_finite_values hM N Q)))%N.
  exact (@finitely_generated_injective_dimension K _ _ _ _
    (nested_to_parent J Q) (@nested_to_parent_injective K C B M N J Q)).
have hlt :
    (dim (chosen_finite_model (subfunctor_finite_values hM (nested_image J) P)) <
     dim (chosen_finite_model (subfunctor_finite_values hM N P)))%N.
  apply: (@finitely_generated_injective_dimension_strict K _ _ _ _
    (nested_to_parent J P) (@nested_to_parent_injective K C B M N J P)).
  exists x => y he; apply: hx; rewrite -he; exact: nested_to_parent_in_J.
rewrite /subfunctor_dimension /mackey_total_dimension (bigD1 i) //=.
rewrite (bigD1 i (F := fun j =>
  dim (chosen_finite_model (subfunctor_finite_values hM N (object_at j)))) ) //= hi.
apply: leq_ltn_trans (leq_add (leqnn _) _) _.
- apply: leq_sum => j _; exact: hle.
- by rewrite ltn_add2r.
Qed.

Theorem finite_nonzero_simple_subfunctor : mackey_nonzero M ->
    exists N : mackey_subfunctor M, mackey_simple (subfunctor_mackey N).
Proof.
move=> [P [x hx]].
have hfull : mackey_nonzero (subfunctor_mackey (full_subfunctor M)).
  exists P, (@submodule_in K (mackey_value M P)
    (subspace_full (mackey_value M P)) x Logic.I) => hz.
  apply: hx; have he := congr1 (@submodule_val K (mackey_value M P)
    (subspace_full (mackey_value M P))) hz.
  change (x = submodule_inclusion (subspace_full (mackey_value M P)) 0) in he.
  by rewrite linear0 in he.
have hex : exists n : nat, `[< exists N : mackey_subfunctor M,
    mackey_nonzero (subfunctor_mackey N) /\ subfunctor_dimension N = n >].
  exists (subfunctor_dimension (full_subfunctor M)); apply/asboolP.
  by exists (full_subfunctor M); split.
have [n /asboolP [N [hN hn]] hmin] := ex_minnP hex.
exists N; split=> // J.
case: (pselect (forall Q y, subfunctor_value J Q y -> y = 0)) => [hzero|hnzero].
  by left.
right=> Q y; case: (pselect (subfunctor_value J Q y)) => // hy.
have hJ : mackey_nonzero (subfunctor_mackey J).
  case: (pselect (mackey_nonzero (subfunctor_mackey J))) => // hnone.
  exfalso; apply: hnzero => T z hz.
  case: (pselect (z = 0)) => // hnz; exfalso; apply: hnone.
  exists T, (submodule_in hz) => he; apply: hnz.
  have hh := congr1 (@submodule_val K (mackey_value (subfunctor_mackey N) T)
    (subfunctor_value J T)) he.
  change (z = submodule_inclusion (subfunctor_value J T) 0) in hh.
  by rewrite linear0 in hh.
have hsmall := nested_proper_dimension_lt (ex_intro _ Q (ex_intro _ y hy)).
have hpred : `[< exists L : mackey_subfunctor M,
    mackey_nonzero (subfunctor_mackey L) /\
      subfunctor_dimension L = subfunctor_dimension (nested_image J) >].
  apply/asboolP; exists (nested_image J); split=> //.
  exact: nested_image_nonzero hJ.
have hbound := hmin _ hpred.
by move: hbound; rewrite -hn leqNgt hsmall.
Qed.

End FiniteSimpleSubobject.

Section Series.
Variable K : fieldType.
Variable C : category.
Variable B : mackey_shape C.

Inductive composition_series : mackey_module K B -> Type :=
| series_zero M of (forall P (x : mackey_value M P), x = 0) : composition_series M
| series_step M (N : mackey_subfunctor M) of
    mackey_simple (subfunctor_mackey N) & composition_series (quotient_mackey N) :
    composition_series M.

Arguments series_zero {M} _.
Arguments series_step {M N} _ _.

Fixpoint series_factors M (s : composition_series M) : seq (mackey_module K B) :=
  match s with
  | @series_zero M _ => [::]
  | @series_step M N _ t => subfunctor_mackey N :: series_factors t
  end.

Lemma series_factors_simple M (s : composition_series M) :
    List.Forall (fun N => mackey_simple N) (series_factors s).
Proof. elim: s => [M0 hz|M0 N hs t ih] //=; constructor=> //. Qed.

Variable I : finType.
Variable object_at : I -> C.
Hypothesis objects_cover : forall P, exists i, object_at i = P.

Theorem finite_composition_series_exists M (hM : mackey_finite_values M) :
    exists s : composition_series M, True.
Proof.
have main : forall n M (hM : mackey_finite_values M),
    mackey_total_dimension object_at hM = n ->
    exists s : composition_series M, True.
  elim/ltn_ind=> n ih M0 h0 hn.
  case: (pselect (mackey_nonzero M0)) => [hnz|hz].
  - have [N hN] := @finite_nonzero_simple_subfunctor K C B I object_at
      objects_cover M0 h0 hnz.
    have hproper : (exists P, exists x, subfunctor_value N P x /\ x <> 0).
      have [P [x hx]] := hN.1.
      exists P, (submodule_val x); split; first exact: submodule_val_mem.
      move=> he; apply: hx; apply: submodule_val_injective.
      change (submodule_val x = submodule_inclusion (subfunctor_value N P) 0).
      by rewrite linear0.
    have hlt : (mackey_total_dimension object_at (quotient_finite_values h0 N) < n)%N.
      rewrite -hn; exact: nonzero_subfunctor_quotient_dimension_lt hproper.
    have [t _] := ih _ hlt (quotient_mackey N) (quotient_finite_values h0 N) erefl.
    exists (series_step hN t); exact Logic.I.
  - have hzero : forall P (x : mackey_value M0 P), x = 0.
      move=> P x; case: (pselect (x = 0)) => // hx.
      exfalso; apply: hz; by exists P, x.
    exists (series_zero hzero); exact Logic.I.
exact: main erefl.
Qed.

End Series.
End DPCompositionSeries.

Print Assumptions DPCompositionSeries.finite_nonzero_simple_subfunctor.
Print Assumptions DPCompositionSeries.finite_composition_series_exists.
Print Assumptions DPCompositionSeries.series_factors_simple.
