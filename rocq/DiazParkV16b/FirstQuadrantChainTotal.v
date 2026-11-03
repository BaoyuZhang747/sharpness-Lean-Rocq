(** The actual finite-diagonal total of a downward bicomplex. *)
From Coq Require Import Arith.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModuleProducts.
From DiazParkV16b Require Import ChainComplex FirstQuadrantChainBicomplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPFirstQuadrantChain.
Local Open Scope ring_scope.
Module DPFirstQuadrantChainTotal.
Section Total.
Variable R : pzRingType.
Variable K : bicomplex R.
Definition total_term n : lmodType R :=
  module_product_type (fun p : nat => module_product_type (fun q : nat =>
    module_product_type (fun _ : (p+q)%coq_nat=n => bicomplex_term K p q))).
Definition horizontal_input p q n (h : (p+q)%coq_nat=n) : (p.+1+q)%coq_nat=n.+1 :=
  f_equal S h.
Definition vertical_input p q n (h : (p+q)%coq_nat=n) : (p+q.+1)%coq_nat=n.+1 :=
  eq_trans (Nat.add_succ_r p q) (f_equal S h).
Definition total_horizontal n (a : total_term n.+1) : total_term n :=
  fun p q h => horizontal K p q (a p.+1 q (horizontal_input h)).
Definition total_vertical n (a : total_term n.+1) : total_term n :=
  fun p q h => (-1:R)^+p *: vertical K p q (a p q.+1 (vertical_input h)).
Lemma total_horizontal_linear n : linear (@total_horizontal n).
Proof.
move=> r a b; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
change (horizontal K p q (r *: a p.+1 q (horizontal_input h)+b p.+1 q (horizontal_input h)) =
 r *: horizontal K p q (a p.+1 q (horizontal_input h)) + horizontal K p q (b p.+1 q (horizontal_input h))).
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@total_horizontal n) (@total_horizontal_linear n).
Lemma total_vertical_linear n : linear (@total_vertical n).
Proof.
move=> r a b; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
change ((-1:R)^+p *: vertical K p q (r *: a p q.+1 (vertical_input h)+b p q.+1 (vertical_input h)) =
 r *: ((-1:R)^+p *: vertical K p q (a p q.+1 (vertical_input h))) + (-1:R)^+p *: vertical K p q (b p q.+1 (vertical_input h))).
by rewrite linearP scalerDr !scalerA commr_sign.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@total_vertical n) (@total_vertical_linear n).
Lemma total_horizontal_squared n (a : total_term n.+2) : total_horizontal (total_horizontal a) = 0.
Proof.
apply functional_extensionality_dep=> p; apply functional_extensionality_dep=> q;
 apply functional_extensionality_dep=> h.
exact: horizontal_squared.
Qed.
Lemma total_vertical_squared n (a : total_term n.+2) : total_vertical (total_vertical a) = 0.
Proof.
apply functional_extensionality_dep=> p; apply functional_extensionality_dep=> q;
 apply functional_extensionality_dep=> h.
change ((-1:R)^+p *: vertical K p q ((-1:R)^+p *: vertical K p q.+1
 (a p q.+2 (vertical_input (vertical_input h)))) = 0).
rewrite linearZ vertical_squared.
change ((-1:R)^+p *: ((-1:R)^+p *: (0 : bicomplex_term K p q)) = 0).
by rewrite !scaler0.
Qed.
Lemma total_mixed_cancel n (a : total_term n.+2) :
 total_horizontal (total_vertical a) + total_vertical (total_horizontal a) = 0.
Proof.
apply functional_extensionality_dep=> p; apply functional_extensionality_dep=> q;
 apply functional_extensionality_dep=> h.
change (horizontal K p q ((-1:R)^+p.+1 *: vertical K p.+1 q
 (a p.+1 q.+1 (vertical_input (horizontal_input h)))) +
 (-1:R)^+p *: vertical K p q (horizontal K p q.+1
 (a p.+1 q.+1 (horizontal_input (vertical_input h)))) = 0).
have he : vertical_input (horizontal_input h) = horizontal_input (vertical_input h) by apply Prop_irrelevance.
rewrite he linearZ horizontal_vertical.
change ((-1:R)^+p.+1 *: vertical K p q (horizontal K p q.+1
 (a p.+1 q.+1 (horizontal_input (vertical_input h)))) +
 (-1:R)^+p *: vertical K p q (horizontal K p q.+1
 (a p.+1 q.+1 (horizontal_input (vertical_input h)))) = 0).
by rewrite exprS mulN1r scaleNr addNr.
Qed.
Definition total_d n (a : total_term n.+1) : total_term n := total_horizontal a + total_vertical a.
Lemma total_d_linear n : linear (@total_d n).
Proof. by move=> r a b; rewrite /total_d !linearP scalerDr addrACA. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@total_d n) (@total_d_linear n).
Lemma total_d_squared n (a : total_term n.+2) : total_d (total_d a) = 0.
Proof.
rewrite /total_d !linearD.
change (total_horizontal (total_horizontal a) + total_horizontal (total_vertical a) +
 (total_vertical (total_horizontal a) + total_vertical (total_vertical a)) = 0).
rewrite total_horizontal_squared total_vertical_squared add0r addr0.
exact: total_mixed_cancel.
Qed.
Definition total_complex : chain_complex R :=
 @ChainComplex R total_term (fun n => (@total_d n : {linear _ -> _})) total_d_squared.
End Total.
End DPFirstQuadrantChainTotal.
