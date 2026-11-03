From mathcomp Require Import all_boot generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FiniteSpans.
Variable C : finite_category.
Variables P Q : fc_object C.

Definition finite_span := {A : fc_object C & (fc_hom C A P * fc_hom C A Q)%type}.
Definition span_object (A : finite_span) := projT1 A.
Definition span_first (A : finite_span) := (projT2 A).1.
Definition span_second (A : finite_span) := (projT2 A).2.

Definition span_factor (A B : finite_span) :=
  {f : fc_hom C (span_object A) (span_object B) |
    (fc_compose f (span_first B) == span_first A) &&
    (fc_compose f (span_second B) == span_second A)}.

Lemma span_factor_first A B (f : span_factor A B) :
    fc_compose (val f) (span_first B) = span_first A.
Proof. exact: eqP (andP (valP f)).1. Qed.

Lemma span_factor_second A B (f : span_factor A B) :
    fc_compose (val f) (span_second B) = span_second A.
Proof. exact: eqP (andP (valP f)).2. Qed.

Definition span_factor_identity (A : finite_span) : span_factor A A.
Proof. exists (fc_identity (span_object A)); by rewrite !fc_id_left !eqxx. Defined.

Definition span_factor_compose (A B D : finite_span)
    (f : span_factor A B) (g : span_factor B D) : span_factor A D.
Proof.
exists (fc_compose (val f) (val g)).
by rewrite !fc_assoc !span_factor_first !span_factor_second !eqxx.
Defined.

Definition finite_span_category : finite_category.
Proof.
refine {| fc_object := [the finType of finite_span];
          fc_hom := fun A B => [the finType of span_factor A B];
          fc_identity := span_factor_identity;
          fc_compose := fun A B D f g => @span_factor_compose A B D f g |}.
- move=> A B f; apply: val_inj; exact: fc_id_left.
- move=> A B f; apply: val_inj; exact: fc_id_right.
- move=> A B D E f g h; apply: val_inj; exact: fc_assoc.
Defined.

Definition span_factor_iso (A B : finite_span) (f : span_factor A B)
    (e : @isomorphism (fc_category C) (span_object A) (span_object B))
    (he : iso_hom e = val f) :
    @isomorphism (fc_category finite_span_category) A B.
Proof.
assert (hi : (fc_compose (iso_inv e) (span_first A) == span_first B) &&
  (fc_compose (iso_inv e) (span_second A) == span_second B)).
{
apply/andP; split; apply/eqP.
- rewrite -(span_factor_first f) -he -fc_assoc.
  have h := iso_inv_hom e.
  change (fc_compose (iso_inv e) (iso_hom e) = fc_identity (span_object B)) in h.
  by rewrite h fc_id_left.
- rewrite -(span_factor_second f) -he -fc_assoc.
  have h := iso_inv_hom e.
  change (fc_compose (iso_inv e) (iso_hom e) = fc_identity (span_object B)) in h.
  by rewrite h fc_id_left.
}
refine (@Build_isomorphism (fc_category finite_span_category) A B f (Sub (iso_inv e) hi) _ _).
- apply: val_inj.
  change (fc_compose (val f) (iso_inv e) = fc_identity (span_object A)).
  rewrite -he; exact (iso_hom_inv e).
- apply: val_inj.
  change (fc_compose (iso_inv e) (val f) = fc_identity (span_object B)).
  rewrite -he; exact (iso_inv_hom e).
Defined.

Lemma span_factor_iso_hom A B f e he : iso_hom (@span_factor_iso A B f e he) = f.
Proof. reflexivity. Qed.

Variable rank : fc_object C -> nat.

Definition span_maximal (A : finite_span) :=
  [forall B : finite_span, forall f : span_factor A B,
    rank (span_object B) <= rank (span_object A)].

Lemma span_maximalP A : reflect
    (forall B, span_factor A B -> rank (span_object B) <= rank (span_object A))
    (span_maximal A).
Proof.
apply: (iffP forallP).
- move=> h B f; exact: forallP (h B) f.
- move=> h B; apply/forallP=> f; exact: h B f.
Qed.

Theorem span_maximal_extension (A : finite_span) :
    exists B : finite_span, span_maximal B /\ exists f : span_factor A B, True.
Proof.
pose reachable B := [exists f : span_factor A B, true].
have hA : reachable A by apply/existsP; exists (span_factor_identity A).
have [B hB hmax] := @arg_maxnP [the finType of finite_span] A reachable
  (fun B => rank (span_object B)) hA.
have /existsP[f _] := hB.
exists B; split; last by exists f.
apply/span_maximalP=> D g; apply: hmax.
apply/existsP; by exists (span_factor_compose f g).
Qed.

Hypothesis hom_rank : forall A B, fc_hom C A B -> rank A <= rank B.
Hypothesis equal_rank_iso : forall A B (f : fc_hom C A B), rank A = rank B ->
  exists e : @isomorphism (fc_category C) A B, iso_hom e = f.

Lemma maximal_factor_isomorphism A B (hA : span_maximal A) (f : span_factor A B) :
    exists e : @isomorphism (fc_category finite_span_category) A B, iso_hom e = f.
Proof.
have /span_maximalP hm := hA.
have hr : rank (span_object A) = rank (span_object B).
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - exact: hom_rank (val f).
  - exact: hm B f.
have [e he] := equal_rank_iso (val f) hr.
exists (span_factor_iso he); exact: span_factor_iso_hom.
Qed.

End FiniteSpans.

Arguments finite_span _ _ _ : clear implicits.
Arguments finite_span_category _ _ _ : clear implicits.
Arguments span_object {_ _ _} _.
Arguments span_first {_ _ _} _.
Arguments span_second {_ _ _} _.

Print Assumptions span_maximal_extension.
Print Assumptions maximal_factor_isomorphism.
