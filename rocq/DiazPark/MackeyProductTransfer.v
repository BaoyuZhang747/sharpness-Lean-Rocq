From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryFiniteProducts CategoryFinitePullbacks
  CategoryFiniteProductComparison CategoryFiniteProductBaseChange MackeyPair.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section ProductTransfer.
Variable R : comPzRingType.
Variable C : category.
Variable M : mackey_pair R C.
Variables P Q : C.

Definition span_section := forall X : C, hom C X P -> hom C X Q -> pair_value M X.
Definition span_section_compatible (x : span_section) :=
  forall X Y (h : hom C X Y) (a : hom C Y P) (b : hom C Y Q),
    x X (compose h a) (compose h b) = pair_pull M h (x Y a b).

Definition product_transfer (D : finite_product_decomposition P Q) (x : span_section) :=
  \sum_(i : fp_index D) pair_push M (fp_right D i)
    (x (fp_apex D i) (fp_left D i) (fp_right D i)).

Lemma product_transfer_comparison (D E : finite_product_decomposition P Q)
    (x : span_section) : span_section_compatible x ->
    product_transfer D x = product_transfer E x.
Proof.
move=> hx; rewrite /product_transfer.
rewrite [RHS](reindex (fp_compare_index D E) (onW_bij _ (fp_compare_index_bijective D E))) /=.
apply: eq_bigr=> i _.
pose e := fp_compare_iso D E i.
have h1 : compose (iso_hom e) (fp_left E (fp_compare_index D E i)) = fp_left D i.
  by rewrite /e fp_compare_iso_hom fp_compare_left.
have h2 : compose (iso_hom e) (fp_right E (fp_compare_index D E i)) = fp_right D i.
  by rewrite /e fp_compare_iso_hom fp_compare_right.
rewrite -h1 -h2 hx pair_push_comp pair_pull_iso.
rewrite -(@pair_push_comp R C M _ _ _ (iso_inv e) (iso_hom e)).
by rewrite iso_inv_hom pair_push_id.
Qed.
End ProductTransfer.

Arguments span_section {R C} M P Q.
Arguments span_section_compatible {R C M P Q} x.
Arguments product_transfer {R C M P Q} D x.

Section BaseChangeTransfer.
Variable R : comPzRingType.
Variable C : category.
Variable M : mackey_pair R C.
Variables P Q Q' : C.
Variable D : finite_product_decomposition P Q.
Variable E : finite_product_decomposition P Q'.
Variable f : hom C Q' Q.
Variable B : forall i : fp_index D, finite_pullback_decomposition (fp_right D i) f.
Hypothesis mackey : forall i (v : pair_value M (fp_apex D i)),
  pair_pull M f (pair_push M (fp_right D i) v) =
  \sum_(j : pb_index (B i)) pair_push M (pb_right (B i) j)
    (pair_pull M (pb_left (B i) j) v).
Variable x : span_section M P Q.
Hypothesis compatible : span_section_compatible x.

Definition span_section_reindex : span_section M P Q' :=
  fun X a b => @x X a (compose b f).

Lemma span_section_reindex_compatible : span_section_compatible span_section_reindex.
Proof. move=> X Y h a b; rewrite /span_section_reindex compose_assoc; exact: compatible. Qed.

Theorem product_transfer_basechange :
    pair_pull M f (product_transfer D x) = product_transfer E span_section_reindex.
Proof.
transitivity (product_transfer (fp_basechange D f B) span_section_reindex).
- rewrite /product_transfer linear_sum.
  under eq_bigr do rewrite mackey.
  rewrite sig_big_dep /=.
  apply: eq_bigr=> [[i j]] _ /=.
  rewrite /span_section_reindex /fp_basechange_right /fp_basechange_left /=.
  rewrite -(pb_commutes (B i) j) compatible.
  reflexivity.
- exact: product_transfer_comparison span_section_reindex_compatible.
Qed.
End BaseChangeTransfer.

Print Assumptions product_transfer_comparison.
Print Assumptions product_transfer_basechange.



