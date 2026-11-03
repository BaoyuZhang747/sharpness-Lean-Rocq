From mathcomp Require Import all_boot.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans
  CategoryFiniteSpanProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GrowthAlignment.
Variable C : finite_category.
Variables P Q : fc_object C.
Variable rank : fc_object C -> nat.
Local Notation Spans := (finite_span C P Q).
Local Notation SC := (finite_span_category C P Q).

Definition span_growth_diamond :=
  forall X A B : Spans, span_maximal rank A -> span_maximal rank B ->
  forall (f : span_factor X A) (g : span_factor X B),
  rank (span_object X) < rank (span_object A) ->
  rank (span_object X) < rank (span_object B) ->
  exists Y Z W : Spans,
  exists (u : span_factor X Y) (v : span_factor Y A)
    (s : span_factor X Z) (t : span_factor Z B)
    (a : span_factor Y W) (b : span_factor Z W),
    rank (span_object X) < rank (span_object Y) /\
    rank (span_object X) < rank (span_object Z) /\
    span_factor_compose u v = f /\ span_factor_compose s t = g /\
    span_factor_compose u a = span_factor_compose s b.

Hypothesis hom_rank : forall A B, fc_hom C A B -> rank A <= rank B.
Hypothesis equal_rank_iso : forall A B (f : fc_hom C A B), rank A = rank B ->
  exists e : @isomorphism (fc_category C) A B, iso_hom e = f.
Hypothesis growth : span_growth_diamond.

Lemma span_align_from_iso X A B (f : span_factor X A) (g : span_factor X B)
    (e : @isomorphism (fc_category SC) X A) (he : iso_hom e = f) :
    exists k : span_factor A B, span_factor_compose f k = g.
Proof.
exists (span_factor_compose (iso_inv e) g).
change ((@fc_compose SC _ _ _) f ((@fc_compose SC _ _ _) (iso_inv e) g) = g).
rewrite -fc_assoc -he.
have h := iso_hom_inv e.
change ((@fc_compose SC _ _ _) (iso_hom e) (iso_inv e) = @fc_identity SC X) in h.
by rewrite h fc_id_left.
Qed.

Theorem span_maximal_alignment_of_growth (X A B : Spans) :
    span_maximal rank A -> span_maximal rank B ->
    forall (f : span_factor X A) (g : span_factor X B),
    exists k : span_factor A B, span_factor_compose f k = g.
Proof.
pose bound := \max_(U : fc_object C) rank U.
have hb U : rank U <= bound := leq_bigmax U.
have rec : forall n (X A B : Spans),
    bound - rank (span_object X) = n ->
    span_maximal rank A -> span_maximal rank B ->
    forall (f : span_factor X A) (g : span_factor X B),
    exists k : span_factor A B, span_factor_compose f k = g.
  elim/ltn_ind=> n ih X0 A0 B0 hn hA hB f g.
  have hf := hom_rank (val f).
  have hg := hom_rank (val g).
  case hfa : (rank (span_object X0) == rank (span_object A0)).
  - have [e he] := equal_rank_iso (val f) (eqP hfa).
    exact: span_align_from_iso (span_factor_iso he) (span_factor_iso_hom he).
  have hfs : rank (span_object X0) < rank (span_object A0).
    by rewrite ltn_neqAle hfa hf.
  case hgb : (rank (span_object X0) == rank (span_object B0)).
  - have [e he] := equal_rank_iso (val g) (eqP hgb).
    have hx := span_maximal_iso hom_rank (span_factor_iso he) hB.
    have [d hd] := maximal_factor_isomorphism hom_rank equal_rank_iso hx f.
    exact: span_align_from_iso d hd.
  have hgs : rank (span_object X0) < rank (span_object B0).
    by rewrite ltn_neqAle hgb hg.
  have [Y [Z [W hd]]] := growth hA hB f g hfs hgs.
  have [u [v [s [t [a [b hd']]]]]] := hd.
  have [hY [hZ [hu [hs hab]]]] := hd'.
  have [E [hE [w _]]] := span_maximal_extension rank W.
  have hnY : bound - rank (span_object Y) < n.
    by rewrite -hn ltn_sub2lE //; exact: hb.
  have hnZ : bound - rank (span_object Z) < n.
    by rewrite -hn ltn_sub2lE //; exact: hb.
  have [kA hkA] := ih _ hnY Y A0 E erefl hA hE v (span_factor_compose a w).
  have [kB hkB] := ih _ hnZ Z B0 E erefl hB hE t (span_factor_compose b w).
  have [e he] := maximal_factor_isomorphism hom_rank equal_rank_iso hB kB.
  have heq : (@fc_compose SC _ _ _) f kA = (@fc_compose SC _ _ _) g kB.
    change ((@fc_compose SC _ _ _) u v = f) in hu.
    change ((@fc_compose SC _ _ _) s t = g) in hs.
    change ((@fc_compose SC _ _ _) v kA = (@fc_compose SC _ _ _) a w) in hkA.
    change ((@fc_compose SC _ _ _) t kB = (@fc_compose SC _ _ _) b w) in hkB.
    change ((@fc_compose SC _ _ _) u a = (@fc_compose SC _ _ _) s b) in hab.
    by rewrite -hu -hs !fc_assoc hkA hkB -!fc_assoc hab.
  exists (span_factor_compose kA (iso_inv e)).
  change ((@fc_compose SC _ _ _) f ((@fc_compose SC _ _ _) kA (iso_inv e)) = g).
  rewrite -fc_assoc heq fc_assoc -he.
  have hh := iso_hom_inv e.
  change ((@fc_compose SC _ _ _) (iso_hom e) (iso_inv e) = @fc_identity SC B0) in hh.
  by rewrite hh fc_id_right.
exact: rec (bound - rank (span_object X)) X A B erefl.
Qed.

End GrowthAlignment.

Print Assumptions span_maximal_alignment_of_growth.
