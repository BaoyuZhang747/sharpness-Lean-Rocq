(** Actual single-component inclusions and finite-column support in the
    diagonal total. These are operations on the constructed module, not
    abstract support axioms. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFirstQuadrantCochain DPFirstQuadrantTotal.
Local Open Scope ring_scope.

Module DPFirstQuadrantSupport.
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

Definition supported_from n (a : total_term K n) k : Prop :=
  forall p q (h : (p + q)%coq_nat = n), (p < k)%coq_nat -> a p q h = 0.

Lemma supported_from_zero n k : supported_from (0 : total_term K n) k.
Proof. by intros p q h hp. Qed.

Lemma supported_from_mono n (a : total_term K n) k l :
    supported_from a k -> (l <= k)%coq_nat -> supported_from a l.
Proof. intros ha hl p q h hp; apply ha; lia. Qed.

Lemma supported_from_add n (a b : total_term K n) k :
    supported_from a k -> supported_from b k -> supported_from (a + b) k.
Proof.
intros ha hb p q h hp; change (a p q h + b p q h = 0).
by rewrite (ha p q h hp) (hb p q h hp) addr0.
Qed.

Lemma supported_from_scale n (a : total_term K n) k r :
    supported_from a k -> supported_from (r *: a) k.
Proof.
intros ha p q h hp; change (r *: a p q h = 0).
by rewrite (ha p q h hp) scaler0.
Qed.

Lemma total_include_supported p q n (hpq : (p + q)%coq_nat = n) (x : bicomplex_term K p q) :
    supported_from (total_include hpq x) p.
Proof. intros r s h hr; apply total_include_other; lia. Qed.

Lemma supported_past_diagonal_zero n (a : total_term K n) :
    supported_from a n.+1 -> a = 0.
Proof.
intro ha; apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intro q.
apply functional_extensionality_dep; intro h.
apply ha; lia.
Qed.

Lemma total_d_supported n (a : total_term K n) k :
    supported_from a k -> supported_from (total_d a) k.
Proof.
intros ha p q h hp.
destruct p as [|p]; destruct q as [|q].
- exfalso; lia.
- change (0 + (-1 : R)^+0 *: vertical K 0%N q (a 0%N q (vertical_index h)) = 0).
  rewrite (ha 0%N q (vertical_index h) hp) linear0 scaler0 addr0; reflexivity.
- change (horizontal K p 0%N (a p 0%N (horizontal_index h)) + 0 = 0).
  have hpk : (p < k)%coq_nat by lia.
  by rewrite (ha p 0%N (horizontal_index h) hpk) linear0 addr0.
- change (horizontal K p q.+1 (a p q.+1 (horizontal_index h)) +
    (-1 : R)^+p.+1 *: vertical K p.+1 q (a p.+1 q (vertical_index h)) = 0).
  have hpk : (p < k)%coq_nat by lia.
  by rewrite (ha p q.+1 (horizontal_index h) hpk) (ha p.+1 q (vertical_index h) hp)
    !linear0 scaler0 addr0.
Qed.
End Support.
End DPFirstQuadrantSupport.
