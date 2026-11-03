From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction CategoryComma
  CategoryStructured CategoryModules CategoryModuleProducts CategoryModuleLimits
  CategoryModuleRightKan CategoryFiniteProducts CategoryFinitePullbacks
  MackeyPair MackeyPairDiagrams MackeyProductTransfer.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Transfer.
Variable R : comPzRingType.
Variable C : category.
Variable M : mackey_pair R C.
Variable Top : C.
Local Notation L := (functor_op (@over_forget C Top)).
Local Notation N := (functor_comp L (pair_codiagram M)).

Definition mackey_slice_ran := fobj (module_ran R L) N.

Definition ran_span_value (Q : C) (x : fobj mackey_slice_ran Q) : span_section M Top Q :=
  fun X a b => module_limit_val x (structured_point L (over_object a) b).

Lemma ran_span_value_compatible (Q : C) (x : fobj mackey_slice_ran Q) :
    span_section_compatible (ran_span_value x).
Proof.
move=> X Y h a b.
pose u := @Build_costructured_hom C C (functor_id C) Top
  (over_object (compose h a)) (over_object a) h erefl.
pose v := @structured_morphism (opposite (over_category C Top)) (opposite C)
  L Q (structured_point L (over_object a) b)
  (structured_point L (over_object (compose h a)) (compose h b)) u erefl.
symmetry; exact (module_limit_val_compatible x v).
Qed.

Lemma ran_span_value_linear (Q X : C) (a : hom C X Top) (b : hom C X Q)
    (r : R) (x y : fobj mackey_slice_ran Q) :
    @ran_span_value Q (r *: x + y) X a b =
      r *: @ran_span_value Q x X a b + @ran_span_value Q y X a b.
Proof.
exact (@module_hom_linear R _ _ (module_limit_projection _
  (structured_point L (over_object a) b)) r x y).
Qed.

Lemma ran_span_value_reindex (Q Q' : C) (f : hom C Q' Q)
    (x : fobj mackey_slice_ran Q) (X : C) (a : hom C X Top) (b : hom C X Q') :
    @ran_span_value Q' (module_hom_fun (fmap mackey_slice_ran f) x) X a b =
    @ran_span_value Q x X a (compose b f).
Proof. reflexivity. Qed.

Variable products : forall Q : C, finite_product_decomposition Top Q.

Definition mackey_ran_transfer_fun (Q : C) (x : fobj mackey_slice_ran Q) : pair_value M Q :=
  product_transfer (products Q) (ran_span_value x).

Lemma mackey_ran_transfer_linear (Q : C) : linear (@mackey_ran_transfer_fun Q).
Proof.
move=> r x y; rewrite /mackey_ran_transfer_fun /product_transfer scaler_sumr -big_split /=.
apply: eq_bigr=> i _.
change (pair_push M (fp_right (products Q) i)
  (@ran_span_value Q (r *: x + y) _ (fp_left (products Q) i) (fp_right (products Q) i)) =
  r *: pair_push M (fp_right (products Q) i)
    (@ran_span_value Q x _ (fp_left (products Q) i) (fp_right (products Q) i)) +
  pair_push M (fp_right (products Q) i)
    (@ran_span_value Q y _ (fp_left (products Q) i) (fp_right (products Q) i))).
by rewrite ran_span_value_linear linearP.
Qed.

Definition mackey_ran_transfer_component (Q : C) :
    module_hom (fobj mackey_slice_ran Q) (pair_value M Q) :=
  exist _ (@mackey_ran_transfer_fun Q) (@mackey_ran_transfer_linear Q).

Variable pullbacks : forall (A B T : C) (f : hom C A T) (g : hom C B T),
  finite_pullback_decomposition f g.
Hypothesis mackey : forall (A B T : C) (f : hom C A T) (g : hom C B T) (x : pair_value M A),
  pair_pull M g (pair_push M f x) =
    \sum_(i : pb_index (pullbacks f g)) pair_push M (pb_right (pullbacks f g) i)
      (pair_pull M (pb_left (pullbacks f g) i) x).

Lemma mackey_ran_transfer_natural (Q Q' : C) (f : hom C Q' Q)
    (x : fobj mackey_slice_ran Q) :
    mackey_ran_transfer_fun (module_hom_fun (fmap mackey_slice_ran f) x) =
      pair_pull M f (mackey_ran_transfer_fun x).
Proof.
symmetry.
rewrite /mackey_ran_transfer_fun.
rewrite (@product_transfer_basechange R C M Top Q Q' (products Q) (products Q') f
  (fun i => pullbacks (fp_right (products Q) i) f)
  (fun i => mackey (fp_right (products Q) i) f) (ran_span_value x)
  (ran_span_value_compatible x)).
apply: eq_bigr=> i _; congr (pair_push M _ _).
Qed.

Definition mackey_ran_transfer : nat_trans mackey_slice_ran (pair_codiagram M).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R) mackey_slice_ran
  (pair_codiagram M) mackey_ran_transfer_component _).
move=> Q Q' f; apply: module_hom_ext=> x; exact: mackey_ran_transfer_natural.
Defined.

Definition mackey_ran_unit : nat_trans (pair_codiagram M) mackey_slice_ran :=
  component (adj_unit (module_ran_adjunction R L)) (pair_codiagram M).

Lemma mackey_ran_unit_transfer (Q : C) (x : pair_value M Q) :
    module_hom_fun (component (nat_comp mackey_ran_unit mackey_ran_transfer) Q) x =
    \sum_(i : fp_index (products Q)) pair_push M (fp_right (products Q) i)
      (pair_pull M (fp_right (products Q) i) x).
Proof. reflexivity. Qed.
End Transfer.

Print Assumptions mackey_ran_transfer.
Print Assumptions mackey_ran_unit_transfer.


