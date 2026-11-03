From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The finite group algebra, with convolution rather than pointwise product.
    Its coefficient ring is allowed to be zero. *)
Section GroupAlgebra.
Variable R : comPzRingType.
Variable G : finGroupType.

Lemma group_regular_scale (a : R) (b : R^o) : a *: b = a * b.
Proof. reflexivity. Qed.

Definition group_algebra := {ffun G -> R^o}.
HB.instance Definition _ := GRing.Lmodule.on group_algebra.

Definition group_basis (g : G) : group_algebra := [ffun h => (g == h)%:R].
Definition group_mul (u v : group_algebra) : group_algebra :=
  \sum_g \sum_h (u g * v h) *: group_basis (g*h)%g.

Lemma group_basis_expansion (u : group_algebra) :
    u = \sum_g u g *: group_basis g.
Proof.
apply/ffunP=> h; rewrite sum_ffunE (bigD1 h) //=.
rewrite ffunE /group_basis ffunE eqxx group_regular_scale mulr1.
rewrite big1 ?addr0 // => g /negbTE hg.
by rewrite ffunE /group_basis ffunE hg group_regular_scale mulr0.
Qed.

Lemma group_mul_addl u v w :
    group_mul (u + v) w = group_mul u w + group_mul v w.
Proof.
rewrite /group_mul -big_split /=; apply: eq_bigr=> g _.
rewrite -big_split /=; apply: eq_bigr=> h _.
by rewrite ffunE mulrDl scalerDl.
Qed.

Lemma group_mul_addr u v w :
    group_mul u (v + w) = group_mul u v + group_mul u w.
Proof.
rewrite /group_mul -big_split /=; apply: eq_bigr=> g _.
rewrite -big_split /=; apply: eq_bigr=> h _.
by rewrite ffunE mulrDr scalerDl.
Qed.

Lemma group_mul_scalel a u v : group_mul (a *: u) v = a *: group_mul u v.
Proof.
rewrite /group_mul scaler_sumr; apply: eq_bigr=> g _.
rewrite scaler_sumr; apply: eq_bigr=> h _.
by rewrite ffunE group_regular_scale scalerA mulrA.
Qed.

Lemma group_mul_scaler a u v : group_mul u (a *: v) = a *: group_mul u v.
Proof.
rewrite /group_mul scaler_sumr; apply: eq_bigr=> g _.
rewrite scaler_sumr; apply: eq_bigr=> h _.
by rewrite ffunE group_regular_scale scalerA mulrCA.
Qed.

Lemma group_mul_linear u : linear (group_mul u).
Proof. by move=> a v w; rewrite group_mul_addr group_mul_scaler. Qed.
HB.instance Definition _ u := GRing.isLinear.Build R
  [the lmodType R of group_algebra] [the lmodType R of group_algebra] _
  (group_mul u) (group_mul_linear u).

Definition group_mul_flip u v := group_mul v u.
Lemma group_mul_flip_linear u : linear (group_mul_flip u).
Proof. by move=> a v w; rewrite /group_mul_flip group_mul_addl group_mul_scalel. Qed.
HB.instance Definition _ u := GRing.isLinear.Build R
  [the lmodType R of group_algebra] [the lmodType R of group_algebra] _
  (group_mul_flip u) (group_mul_flip_linear u).

Lemma group_mul_basis g h : group_mul (group_basis g) (group_basis h) =
    group_basis (g*h)%g.
Proof.
rewrite /group_mul (bigD1 g) //=.
have hz : \sum_(a | a != g) \sum_b
    (group_basis g a * group_basis h b) *: group_basis (a*b)%g = 0.
  apply: big1=> a /negbTE ha; apply: big1=> b _.
  by rewrite /group_basis !ffunE eq_sym ha mul0r scale0r.
rewrite hz addr0 (bigD1 h) //=.
rewrite /group_basis !ffunE !eqxx mul1r scale1r.
rewrite big1 ?addr0 // => b /negbTE hb.
by rewrite !ffunE eq_sym hb mul1r scale0r.
Qed.

Lemma group_mul_expandl u v :
    group_mul u v = \sum_g u g *: group_mul (group_basis g) v.
Proof.
change (group_mul_flip v u = \sum_g u g *: group_mul (group_basis g) v).
rewrite {1}[u]group_basis_expansion linear_sum.
by under eq_bigr do rewrite linearZ.
Qed.

Lemma group_mul_expandr u v :
    group_mul u v = \sum_h v h *: group_mul u (group_basis h).
Proof.
rewrite {1}[v]group_basis_expansion linear_sum.
by under eq_bigr do rewrite linearZ.
Qed.

Lemma group_mul_suml (I : finType) (f : I -> group_algebra) v :
    group_mul (\sum_i f i) v = \sum_i group_mul (f i) v.
Proof. exact: (linear_sum (group_mul_flip v) _ _ _). Qed.

Local Opaque group_mul group_basis.

Lemma group_mulA : associative group_mul.
Proof.
move=> u v w.
rewrite (group_mul_expandl u (group_mul v w)).
rewrite (group_mul_expandl u v) group_mul_suml.
apply: eq_bigr=> g _; rewrite group_mul_scalel; congr (_ *: _).
rewrite (group_mul_expandl v w) linear_sum.
rewrite (group_mul_expandr (group_basis g) v) group_mul_suml.
apply: eq_bigr=> h _; rewrite linearZ /= group_mul_scalel; congr (_ *: _).
rewrite (group_mul_expandr (group_basis h) w) linear_sum.
rewrite (group_mul_expandr (group_mul (group_basis g) (group_basis h)) w).
apply: eq_bigr=> k _; by rewrite linearZ /= !group_mul_basis mulgA.
Qed.
Lemma group_mul1 : left_id (group_basis 1%g) group_mul.
Proof.
move=> u; rewrite {1}[u]group_basis_expansion linear_sum.
under eq_bigr do rewrite linearZ /= group_mul_basis mul1g.
exact: esym (group_basis_expansion u).
Qed.

Lemma group_mulr1 : right_id (group_basis 1%g) group_mul.
Proof.
move=> u; rewrite {1}[u]group_basis_expansion group_mul_suml.
under eq_bigr do rewrite group_mul_scalel group_mul_basis mulg1.
exact: esym (group_basis_expansion u).
Qed.

HB.instance Definition _ := GRing.Zmodule_isPzRing.Build group_algebra
  group_mulA group_mul1 group_mulr1 group_mul_addl group_mul_addr.

Lemma group_algebra_basis_mul g h :
    group_basis g * group_basis h = group_basis (g*h)%g.
Proof. exact: group_mul_basis. Qed.

Lemma group_algebra_one : (1 : group_algebra) = group_basis 1%g.
Proof. reflexivity. Qed.

End GroupAlgebra.











