From mathcomp Require Import all_boot all_algebra boolp vector.
From DiazPark Require Import Category ModuleInfrastructure MackeyStructures
  MackeySubquotients MackeyModuleCarriers MackeyModuleMaps MackeyModuleQuotient
  ModuleFiniteDimensional ModuleFiniteSubmodules ModuleFiniteDimensionMaps.

(** Finite length is proved for the original arbitrary-module Mackey objects
    once their values are finitely generated over a field. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FiniteLength.
Variable K : fieldType.
Variable C : category.
Variable B : mackey_shape C.
Variable I : finType.
Variable object_at : I -> C.
Hypothesis objects_cover : forall P, exists i, object_at i = P.

Definition mackey_finite_values (M : mackey_module K B) :=
  forall P, module_finitely_generated (mackey_value M P).

Definition mackey_total_dimension (M : mackey_module K B)
    (hM : mackey_finite_values M) : nat :=
  \sum_i dim (chosen_finite_model (hM (object_at i))).

Variable M : mackey_module K B.
Variable hM : mackey_finite_values M.
Variable N : mackey_subfunctor M.

Definition subfunctor_finite_values : mackey_finite_values (subfunctor_mackey N) :=
  fun P => field_finitely_generated_submodule (hM P) (subfunctor_value N P).

Definition quotient_finite_values : mackey_finite_values (quotient_mackey N) :=
  fun P => field_finitely_generated_quotient (hM P) (subfunctor_value N P).

Lemma subfunctor_value_dimension_le P :
    (dim (chosen_finite_model (subfunctor_finite_values P)) <=
      dim (chosen_finite_model (hM P)))%N.
Proof.
exact (@finitely_generated_injective_dimension K _ _
  (subfunctor_finite_values P) (hM P) (submodule_inclusion (subfunctor_value N P))
  (@submodule_val_injective K _ (subfunctor_value N P))).
Qed.

Lemma quotient_value_dimension_le P :
    (dim (chosen_finite_model (quotient_finite_values P)) <=
      dim (chosen_finite_model (hM P)))%N.
Proof.
exact (@finitely_generated_surjective_dimension K _ _
  (hM P) (quotient_finite_values P)
  (quotient_pi (subfunctor_value N P) : {linear _ -> _})
  (@quotient_pi_surjective K _ (subfunctor_value N P))).
Qed.

Lemma proper_subfunctor_dimension_lt :
    (exists P, exists x, ~ subfunctor_value N P x) ->
    (mackey_total_dimension subfunctor_finite_values < mackey_total_dimension hM)%N.
Proof.
move=> [P [x hx]]; have [i hi] := objects_cover P.
have hlt : (dim (chosen_finite_model (subfunctor_finite_values P)) <
    dim (chosen_finite_model (hM P)))%N.
  apply: (@finitely_generated_injective_dimension_strict K _ _
    (subfunctor_finite_values P) (hM P)
    (submodule_inclusion (subfunctor_value N P))).
  - exact: submodule_val_injective.
  - exists x => y he; apply: hx; rewrite -he; exact: submodule_val_mem.
rewrite /mackey_total_dimension (bigD1 i) //=.
rewrite (bigD1 i (F := fun j => dim (chosen_finite_model (hM (object_at j)))) ) //= hi.
apply: leq_ltn_trans (leq_add (leqnn _) _) _.
- apply: leq_sum => j _; exact: subfunctor_value_dimension_le.
- by rewrite ltn_add2r.
Qed.

Lemma nonzero_subfunctor_quotient_dimension_lt :
    (exists P, exists x, subfunctor_value N P x /\ x <> 0) ->
    (mackey_total_dimension quotient_finite_values < mackey_total_dimension hM)%N.
Proof.
move=> [P [x [hx hn]]]; have [i hi] := objects_cover P.
have hlt : (dim (chosen_finite_model (quotient_finite_values P)) <
    dim (chosen_finite_model (hM P)))%N.
  apply: (@finitely_generated_surjective_dimension_strict K _ _
    (hM P) (quotient_finite_values P)
    (quotient_pi (subfunctor_value N P) : {linear _ -> _})).
  - exact: quotient_pi_surjective.
  - exists x; split=> //; apply/quotient_pi_kernel; exact hx.
rewrite /mackey_total_dimension (bigD1 i) //=.
rewrite (bigD1 i (F := fun j => dim (chosen_finite_model (hM (object_at j)))) ) //= hi.
apply: leq_ltn_trans (leq_add (leqnn _) _) _.
- apply: leq_sum => j _; exact: quotient_value_dimension_le.
- by rewrite ltn_add2r.
Qed.

End FiniteLength.

Section FiniteLengthInduction.
Variable K : fieldType.
Variable C : category.
Variable B : mackey_shape C.
Variable I : finType.
Variable object_at : I -> C.
Hypothesis objects_cover : forall P, exists i, object_at i = P.
Variable property : mackey_module K B -> Prop.
Hypothesis property_zero : forall M, (forall P (x : mackey_value M P), x = 0) -> property M.
Hypothesis property_simple : forall M, mackey_simple M -> property M.
Hypothesis property_extension : forall M (N : mackey_subfunctor M),
  property (subfunctor_mackey N) -> property (quotient_mackey N) -> property M.

Theorem finite_mackey_induction M (hM : mackey_finite_values M) : property M.
Proof.
have main : forall n M (hM : mackey_finite_values M),
    mackey_total_dimension object_at hM = n -> property M.
  elim/ltn_ind=> n ih M0 h0 hn.
  case: (pselect (mackey_nonzero M0)) => [hnz|hz].
  2: apply: property_zero => P x; case: (pselect (x = 0)) => // hx;
     exfalso; apply: hz; by exists P, x.
  case: (pselect (mackey_simple M0)) => [hs|hns]; first exact: property_simple hs.
  have hex : exists N : mackey_subfunctor M0,
      (exists P, exists x, subfunctor_value N P x /\ x <> 0) /\
      (exists P, exists x, ~ subfunctor_value N P x).
    case: (pselect (exists N : mackey_subfunctor M0,
      (exists P, exists x, subfunctor_value N P x /\ x <> 0) /\
      (exists P, exists x, ~ subfunctor_value N P x))) => // hnone.
    exfalso; apply: hns; split=> // N.
    case: (pselect (exists P, exists x, subfunctor_value N P x /\ x <> 0)) => [hNZ|hZ].
    - right=> P x; case: (pselect (subfunctor_value N P x)) => // hx.
      exfalso; apply: hnone; exists N; split=> //; by exists P, x.
    - left=> P x hx; case: (pselect (x = 0)) => // hn0.
      exfalso; apply: hZ; exists P, x; by split.
  have [N [hNZ hproper]] := hex; apply: (@property_extension M0 N).
  - apply: (ih _ _ (subfunctor_mackey N) (subfunctor_finite_values h0 N) erefl).
    rewrite -hn; exact (@proper_subfunctor_dimension_lt K C B I object_at
      objects_cover M0 h0 N hproper).
  - apply: (ih _ _ (quotient_mackey N) (quotient_finite_values h0 N) erefl).
    rewrite -hn; exact (@nonzero_subfunctor_quotient_dimension_lt K C B I object_at
      objects_cover M0 h0 N hNZ).
exact: main erefl.
Qed.

End FiniteLengthInduction.
