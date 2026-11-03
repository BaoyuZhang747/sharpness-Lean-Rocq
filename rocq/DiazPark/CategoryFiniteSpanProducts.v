From mathcomp Require Import all_boot generic_quotient boolp.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses
  CategoryFiniteProducts CategoryFiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope quotient_scope.

Section MaximalSpanProducts.
Variable C : finite_category.
Variables P Q : fc_object C.
Variable rank : fc_object C -> nat.
Hypothesis hom_rank : forall A B, fc_hom C A B -> rank A <= rank B.
Hypothesis equal_rank_iso : forall A B (f : fc_hom C A B), rank A = rank B ->
  exists e : @isomorphism (fc_category C) A B, iso_hom e = f.
Local Notation Spans := (finite_span C P Q).
Local Notation SC := (finite_span_category C P Q).

Hypothesis maximal_alignment : forall X A B : Spans,
  span_maximal rank A -> span_maximal rank B ->
  forall (f : span_factor X A) (g : span_factor X B),
  exists k : span_factor A B, span_factor_compose f k = g.

Hypothesis maximal_rigidity : forall A : Spans, span_maximal rank A ->
  forall f : span_factor A A, val f = fc_identity (span_object A).

Lemma span_maximal_iso A B (e : @isomorphism (fc_category SC) A B) :
    span_maximal rank B -> span_maximal rank A.
Proof.
move/span_maximalP=> hB; apply/span_maximalP=> D f.
exact (leq_trans (hB D (span_factor_compose (iso_inv e) f))
  (hom_rank (val (iso_inv e)))).
Qed.

Definition maximal_span_index :=
  {a : fc_iso_class SC | span_maximal rank (repr a)}.

Definition maximal_span_representative (i : maximal_span_index) : Spans := repr (val i).

Definition maximal_span_class (A : Spans) (hA : span_maximal rank A) : maximal_span_index.
Proof.
exists (@fc_class SC A); exact: span_maximal_iso (@fc_repr_iso SC A) hA.
Defined.

Lemma maximal_span_class_value A hA :
    val (@maximal_span_class A hA) = @fc_class SC A.
Proof. reflexivity. Qed.

Definition maximal_span_choice (A : Spans) :=
  proj1_sig (cid (span_maximal_extension rank A)).

Lemma maximal_span_choice_maximal A : span_maximal rank (maximal_span_choice A).
Proof. exact (proj1 (proj2_sig (cid (span_maximal_extension rank A)))). Qed.

Lemma maximal_span_choice_factor_exists A :
    exists f : span_factor A (maximal_span_choice A), True.
Proof. exact (proj2 (proj2_sig (cid (span_maximal_extension rank A)))). Qed.

Definition maximal_span_choice_factor A :=
  proj1_sig (cid (maximal_span_choice_factor_exists A)).

Definition maximal_span_lift (A : Spans) :
    {i : maximal_span_index & span_factor A (maximal_span_representative i)}.
Proof.
refine (existT _ (maximal_span_class (maximal_span_choice_maximal A)) _).
exact (span_factor_compose (maximal_span_choice_factor A)
  (iso_inv (@fc_repr_iso SC (maximal_span_choice A)))).
Defined.

Lemma maximal_span_pair_unique (A : Spans)
    (t u : {i : maximal_span_index & span_factor A (maximal_span_representative i)}) :
    t = u.
Proof.
case: t=> i f; case: u=> j g.
have [k hk] := maximal_alignment (valP i) (valP j) f g.
have [e he] := maximal_factor_isomorphism hom_rank equal_rank_iso (valP i) k.
have hc : @fc_class SC (maximal_span_representative i) =
    @fc_class SC (maximal_span_representative j).
  apply/fc_class_eq; exact: fc_related_of_iso e.
have hij : i = j.
  apply: val_inj; by move: hc; rewrite /maximal_span_representative /fc_class !reprK.
destruct hij.
have hv : val f = val g.
  have hh := congr1 val hk.
  change (fc_compose (val f) (val k) = val g) in hh.
  by rewrite (maximal_rigidity (valP i) k) fc_id_right in hh.
have hfg : f = g := val_inj hv.
by rewrite hfg.
Qed.

Definition span_of_pair (X : fc_object C) (f : fc_hom C X P) (g : fc_hom C X Q) : Spans :=
  existT _ X (f, g).

Definition maximal_product_lift X (f : fc_hom C X P) (g : fc_hom C X Q) :
    {i : maximal_span_index & fc_hom C X (span_object (maximal_span_representative i))} :=
  let t := maximal_span_lift (span_of_pair f g) in
  existT _ (projT1 t) (val (projT2 t)).

Lemma maximal_product_lift_first X (f : fc_hom C X P) (g : fc_hom C X Q) :
    fc_compose (projT2 (maximal_product_lift f g))
      (span_first (maximal_span_representative (projT1 (maximal_product_lift f g)))) = f.
Proof. exact (span_factor_first (projT2 (maximal_span_lift (span_of_pair f g)))). Qed.

Lemma maximal_product_lift_second X (f : fc_hom C X P) (g : fc_hom C X Q) :
    fc_compose (projT2 (maximal_product_lift f g))
      (span_second (maximal_span_representative (projT1 (maximal_product_lift f g)))) = g.
Proof. exact (span_factor_second (projT2 (maximal_span_lift (span_of_pair f g)))). Qed.

Lemma maximal_product_lift_unique X i
    (h : fc_hom C X (span_object (maximal_span_representative i))) :
    maximal_product_lift (fc_compose h (span_first (maximal_span_representative i)))
      (fc_compose h (span_second (maximal_span_representative i))) =
      existT (fun j => fc_hom C X (span_object (maximal_span_representative j))) i h.
Proof.
pose A := span_of_pair (fc_compose h (span_first (maximal_span_representative i)))
  (fc_compose h (span_second (maximal_span_representative i))).
assert (hh : (fc_compose h (span_first (maximal_span_representative i)) == span_first A) &&
  (fc_compose h (span_second (maximal_span_representative i)) == span_second A)).
{ by rewrite /A /span_of_pair /span_first /span_second /= !eqxx. }
pose f : span_factor A (maximal_span_representative i) := Sub h hh.
have he := maximal_span_pair_unique (maximal_span_lift A) (existT _ i f).
exact (congr1 (fun t : {j : maximal_span_index & span_factor A (maximal_span_representative j)} =>
  existT (fun j => fc_hom C X (span_object (maximal_span_representative j)))
    (projT1 t) (val (projT2 t))) he).
Qed.

Definition finite_product_of_maximal_spans :
    @finite_product_decomposition (fc_category C) P Q :=
  @Build_finite_product_decomposition (fc_category C) P Q
    [the finType of maximal_span_index]
    (fun i => span_object (maximal_span_representative i))
    (fun i => span_first (maximal_span_representative i))
    (fun i => span_second (maximal_span_representative i))
    (@maximal_product_lift) (@maximal_product_lift_first)
    (@maximal_product_lift_second) (@maximal_product_lift_unique).

End MaximalSpanProducts.

Print Assumptions maximal_span_pair_unique.
Print Assumptions finite_product_of_maximal_spans.
