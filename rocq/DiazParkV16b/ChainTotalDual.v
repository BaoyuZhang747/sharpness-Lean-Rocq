(** Actual finite-diagonal Hom duality, with literal coordinate inclusions and finite-sum inverse. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalModuleIso.
From DiazParkV16b Require Import LinearMapSpace FirstQuadrantChainBicomplex FirstQuadrantChainTotal
  FirstQuadrantChainTotalSupport FirstQuadrantChainTotalProjective
  FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPLinearMapSpace DPFirstQuadrantChain
  DPFirstQuadrantChainTotal DPFirstQuadrantChainSupport DPFirstQuadrantChainTotalProjective.
Local Open Scope ring_scope.

Module DPChainTotalDual.
Section Dual.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable K : bicomplex R.

Definition dual_horizontal p q := @precompose R (bicomplex_term K p q) A
  (bicomplex_term K p.+1 q) (horizontal K p q).
Definition dual_vertical p q := @precompose R (bicomplex_term K p q) A
  (bicomplex_term K p q.+1) (vertical K p q).
Lemma dual_horizontal_squared p q f : dual_horizontal p.+1 q (dual_horizontal p q f) = 0.
Proof.
apply ext => x; change (as_linear f (horizontal K p q (horizontal K p.+1 q x)) = 0).
by rewrite horizontal_squared linear0.
Qed.
Lemma dual_vertical_squared p q f : dual_vertical p q.+1 (dual_vertical p q f) = 0.
Proof.
apply ext => x; change (as_linear f (vertical K p q (vertical K p q.+1 x)) = 0).
by rewrite vertical_squared linear0.
Qed.
Lemma dual_horizontal_vertical p q f :
  dual_horizontal p q.+1 (dual_vertical p q f) = dual_vertical p.+1 q (dual_horizontal p q f).
Proof.
apply ext => x; change (evaluate f (vertical K p q (horizontal K p q.+1 x)) =
  evaluate f (horizontal K p q (vertical K p.+1 q x))).
by rewrite horizontal_vertical.
Qed.
Definition dual_bicomplex : DPFirstQuadrantCochain.bicomplex R :=
  @DPFirstQuadrantCochain.Bicomplex R (fun p q => linear_maps (bicomplex_term K p q) A)
    dual_horizontal dual_vertical dual_horizontal_squared dual_vertical_squared dual_horizontal_vertical.

Definition total_dual_forward n (f : linear_maps (total_term K n) A) :
  DPFirstQuadrantTotal.total_term dual_bicomplex n :=
  fun p q h => @precompose R (total_term K n) A (bicomplex_term K p q) (@total_include R K p q n h) f.
Lemma total_dual_forward_linear n : linear (@total_dual_forward n).
Proof.
move=> r f g; apply functional_extensionality_dep => p; apply functional_extensionality_dep => q;
  apply functional_extensionality_dep => h; apply ext => x; reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (@total_dual_forward n) (@total_dual_forward_linear n).
Lemma total_dual_forward_evaluate n f p q h x :
  evaluate (@total_dual_forward n f p q h) x = evaluate f (@total_include R K p q n h x).
Proof. reflexivity. Qed.

Definition total_dual_inverse_eval n (a : DPFirstQuadrantTotal.total_term dual_bicomplex n)
  (x : total_term K n) : A :=
  \sum_(i : 'I_n.+1) evaluate (a (val i) (diagonal_second i) (diagonal_equation i))
    (x (val i) (diagonal_second i) (diagonal_equation i)).
Lemma total_dual_inverse_eval_linear n (a : DPFirstQuadrantTotal.total_term dual_bicomplex n) :
  linear (@total_dual_inverse_eval n a).
Proof.
move=> r x y; rewrite /total_dual_inverse_eval scaler_sumr -big_split.
apply eq_bigr => i _; exact: linearP.
Qed.
HB.instance Definition _ n a := GRing.isLinear.Build R _ _ _
  (@total_dual_inverse_eval n a) (@total_dual_inverse_eval_linear n a).
Definition total_dual_inverse n (a : DPFirstQuadrantTotal.total_term dual_bicomplex n) :
  linear_maps (total_term K n) A := of_linear (@total_dual_inverse_eval n a).
Lemma total_dual_inverse_linear n : linear (@total_dual_inverse n).
Proof.
move=> r a b; apply ext => x.
change (@total_dual_inverse_eval n (r *: a+b) x =
  r *: @total_dual_inverse_eval n a x + @total_dual_inverse_eval n b x).
rewrite /total_dual_inverse_eval scaler_sumr -big_split.
apply eq_bigr => i _; reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (@total_dual_inverse n) (@total_dual_inverse_linear n).

Theorem total_dual_forwardK n (f : linear_maps (total_term K n) A) :
  total_dual_inverse (total_dual_forward f) = f.
Proof.
apply ext => x.
change (\sum_(i : 'I_n.+1) as_linear f (diagonal_piece i x) = as_linear f x).
by rewrite -linear_sum total_diagonal_decomposition.
Qed.

Lemma total_dual_inverse_include n (a : DPFirstQuadrantTotal.total_term dual_bicomplex n)
  p q (h : (p+q)%coq_nat=n) (x : bicomplex_term K p q) :
  evaluate (total_dual_inverse a) (@total_include R K p q n h x) = evaluate (a p q h) x.
Proof.
change (\sum_(i : 'I_n.+1) evaluate (a (val i) (diagonal_second i) (diagonal_equation i))
  (@total_include R K p q n h x (val i) (diagonal_second i) (diagonal_equation i)) = evaluate (a p q h) x).
have hp : (p < n.+1)%N by apply/ltP; lia.
pose j : 'I_n.+1 := Ordinal hp.
rewrite (bigD1 j) //=.
have hj : diagonal_second j = q by unfold diagonal_second; change ((n-p)%coq_nat=q); lia.
have hm : evaluate (a (val j) (diagonal_second j) (diagonal_equation j))
    (@total_include R K p q n h x (val j) (diagonal_second j) (diagonal_equation j)) = evaluate (a p q h) x.
  change (evaluate (a p (diagonal_second j) (diagonal_equation j))
    (@total_include R K p q n h x p (diagonal_second j) (diagonal_equation j)) = evaluate (a p q h) x).
  move: (diagonal_equation j); rewrite hj; move=> hh.
  rewrite total_include_same.
  have he : hh=h by apply Prop_irrelevance.
  by rewrite he.
rewrite hm.
have hz : \sum_(i : 'I_n.+1 | i != j) evaluate (a (val i) (diagonal_second i) (diagonal_equation i))
    (@total_include R K p q n h x (val i) (diagonal_second i) (diagonal_equation i)) = 0.
  apply big1 => i hi.
  have he : p <> val i.
    move=> e; have eij : i=j by apply val_inj; symmetry; exact e.
    by rewrite eij eqxx in hi.
  rewrite (@total_include_other R K p q n h x (val i) (diagonal_second i) (diagonal_equation i) he); exact: linear0.
by rewrite hz addr0.
Qed.
Theorem total_dual_inverseK n (a : DPFirstQuadrantTotal.total_term dual_bicomplex n) :
  total_dual_forward (total_dual_inverse a) = a.
Proof.
apply functional_extensionality_dep => p; apply functional_extensionality_dep => q;
  apply functional_extensionality_dep => h; apply ext => x.
exact: total_dual_inverse_include.
Qed.
Definition total_dual_degree_iso n : @isomorphism (module_category R)
  (linear_maps (total_term K n) A) (DPFirstQuadrantTotal.total_term dual_bicomplex n).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (@total_dual_forward n)) (module_hom_of_linear (@total_dual_inverse n)) _ _).
- apply module_hom_ext => f; exact: total_dual_forwardK.
- apply module_hom_ext => a; exact: total_dual_inverseK.
Defined.
End Dual.
End DPChainTotalDual.
