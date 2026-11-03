(** Actual single-component inclusions and finite-column support in the
    diagonal total. These are operations on the constructed module, not
    abstract support axioms. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazParkV16b Require Import ChainComplex.
From DiazParkV16b Require Import FirstQuadrantChainBicomplex FirstQuadrantChainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPFirstQuadrantChain DPFirstQuadrantChainTotal.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainSupport.
Section Support.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition total_include p q n (hpq : (p + q)%coq_nat = n) (x : bicomplex_term K p q) :
    total_term K n := fun r s _ =>
  match Nat.eq_dec p r with
  | left ep => match Nat.eq_dec q s with
    | left eq => eq_rect q (fun t => bicomplex_term K r t)
        (eq_rect p (fun t => bicomplex_term K t q) x r ep) s eq
    | right _ => 0 end
  | right _ => 0 end.

Lemma total_include_linear p q n (hpq : (p + q)%coq_nat = n) : linear (@total_include p q n hpq).
Proof.
intros a x y; apply functional_extensionality_dep; intro r.
apply functional_extensionality_dep; intro s.
apply functional_extensionality_dep; intro h.
change (@total_include p q n hpq (a *: x + y) r s h =
  a *: @total_include p q n hpq x r s h + @total_include p q n hpq y r s h).
unfold total_include.
destruct (Nat.eq_dec p r) as [ep|ep]; [destruct ep|].
- destruct (Nat.eq_dec q s) as [eq|eq]; [destruct eq|].
  + reflexivity.
  + change (0 = a *: (0 : bicomplex_term K p s) + 0); by rewrite scaler0 addr0.
- change (0 = a *: (0 : bicomplex_term K r s) + 0); by rewrite scaler0 addr0.
Qed.
HB.instance Definition _ p q n hpq := GRing.isLinear.Build R (bicomplex_term K p q) (total_term K n)
  _ (@total_include p q n hpq) (@total_include_linear p q n hpq).

Lemma total_include_same p q n (hpq h : (p + q)%coq_nat = n) (x : bicomplex_term K p q) :
    @total_include p q n hpq x p q h = x.
Proof.
unfold total_include.
destruct (Nat.eq_dec p p) as [ep|ep]; [|contradiction].
destruct (Nat.eq_dec q q) as [eq|eq]; [|contradiction].
replace ep with (@Logic.eq_refl nat p) by apply Prop_irrelevance.
replace eq with (@Logic.eq_refl nat q) by apply Prop_irrelevance.
reflexivity.
Qed.

Lemma total_include_other p q n (hpq : (p + q)%coq_nat = n)
    (x : bicomplex_term K p q) r s (h : (r + s)%coq_nat = n) :
    p <> r -> @total_include p q n hpq x r s h = 0.
Proof. intro hn; unfold total_include; destruct (Nat.eq_dec p r); [contradiction|reflexivity]. Qed.

Definition supported_before n (a : total_term K n) k : Prop :=
 forall p q (h : (p+q)%coq_nat=n), (k <= p)%coq_nat -> a p q h = 0.
Lemma supported_before_zero n (a : total_term K n) : supported_before a 0%N -> a=0.
Proof.
move=> ha; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
apply ha; lia.
Qed.
Lemma supported_diagonal n (a : total_term K n) : supported_before a n.+1.
Proof. move=> p q h hp; exfalso; lia. Qed.
Lemma total_d_supported n (a : total_term K n.+1) k :
 supported_before a k -> supported_before (total_d a) k.
Proof.
move=> ha p q h hp.
change (horizontal K p q (a p.+1 q (horizontal_input h))+
 (-1:R)^+p *: vertical K p q (a p q.+1 (vertical_input h))=0).
have hp1 : (k<=p.+1)%coq_nat by lia.
by rewrite (ha _ _ _ hp1) (ha _ _ _ hp) !linear0 scaler0 addr0.
Qed.
Lemma total_include_supported p q n (h : (p+q)%coq_nat=n) (x : bicomplex_term K p q) :
 supported_before (total_include h x) p.+1.
Proof. move=> r s hs hr; apply total_include_other; lia. Qed.
End Support.
End DPFirstQuadrantChainSupport.
