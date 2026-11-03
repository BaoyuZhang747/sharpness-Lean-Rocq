From mathcomp Require Import all_boot.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Transport.
Variable C : finite_category.
Variables P Q : fc_object C.
Variable rank : fc_object C -> nat.
Hypothesis hom_rank : forall A B, fc_hom C A B -> rank A <= rank B.
Local Notation Spans := (finite_span C P Q).
Local Notation SC := (finite_span_category C P Q).
Local Notation comp := (@fc_compose SC _ _ _).

Lemma span_isomorphism_rank (X X' : Spans)
    (e : @isomorphism (fc_category SC) X X') :
    rank (span_object X) = rank (span_object X').
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: hom_rank (val (iso_hom e)).
- exact: hom_rank (val (iso_inv e)).
Qed.

Lemma span_diamond_transport (X A B X' A' B' : Spans)
    (eX : @isomorphism (fc_category SC) X X')
    (eA : @isomorphism (fc_category SC) A A')
    (eB : @isomorphism (fc_category SC) B B')
    (f : span_factor X A) (g : span_factor X B)
    (f' : span_factor X' A') (g' : span_factor X' B')
    (hf : comp (iso_hom eX) f' = comp f (iso_hom eA))
    (hg : comp (iso_hom eX) g' = comp g (iso_hom eB))
    (Y Z W : Spans)
    (u : span_factor X' Y) (v : span_factor Y A')
    (s : span_factor X' Z) (t : span_factor Z B')
    (a : span_factor Y W) (b : span_factor Z W) :
    rank (span_object X') < rank (span_object Y) ->
    rank (span_object X') < rank (span_object Z) ->
    comp u v = f' -> comp s t = g' -> comp u a = comp s b ->
    exists (u0 : span_factor X Y) (v0 : span_factor Y A)
      (s0 : span_factor X Z) (t0 : span_factor Z B),
      rank (span_object X) < rank (span_object Y) /\
      rank (span_object X) < rank (span_object Z) /\
      comp u0 v0 = f /\ comp s0 t0 = g /\ comp u0 a = comp s0 b.
Proof.
move=> hY hZ hu hs hab.
exists (comp (iso_hom eX) u), (comp v (iso_inv eA)),
  (comp (iso_hom eX) s), (comp t (iso_inv eB)).
split; first by rewrite (span_isomorphism_rank eX).
split; first by rewrite (span_isomorphism_rank eX).
split.
- rewrite fc_assoc -(@fc_assoc SC _ _ _ _ u v (iso_inv eA)) hu -fc_assoc hf fc_assoc.
  have h := iso_hom_inv eA.
  change (comp (iso_hom eA) (iso_inv eA) = @fc_identity SC A) in h.
  by rewrite h fc_id_right.
split.
- rewrite fc_assoc -(@fc_assoc SC _ _ _ _ s t (iso_inv eB)) hs -fc_assoc hg fc_assoc.
  have h := iso_hom_inv eB.
  change (comp (iso_hom eB) (iso_inv eB) = @fc_identity SC B) in h.
  by rewrite h fc_id_right.
by rewrite !fc_assoc hab.
Qed.
End Transport.

Print Assumptions span_diamond_transport.

