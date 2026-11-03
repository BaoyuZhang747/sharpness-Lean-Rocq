From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra generic_quotient.
From DiazPark Require Import Category CategoryFiniteProducts CategoryFinite
  CategoryFiniteClasses.

(** The free coefficient module is indexed by actual isomorphism classes.
    Products are the actual apex sums from universal representable products.
    No multiplicativity of marks is included as an input. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Section FreeBurnsideModule.
Variable C : finite_category.
Variable R : comPzRingType.

Lemma burnside_regular_scale (a : R) (b : R^o) : a *: b = a * b.
Proof. reflexivity. Qed.

Definition burnside_module := {ffun fc_iso_class C -> R^o}.
Definition burnside_basis (a : fc_iso_class C) : burnside_module :=
  [ffun b => (a == b)%:R].
Definition burnside_mark (X : fc_object C) (v : burnside_module) : R :=
  \sum_a v a * (fc_mark X a)%:R.

Lemma burnside_mark_linear X : linear
    (burnside_mark X : [the lmodType R of burnside_module] -> R^o).
Proof.
move=> a v w; rewrite /burnside_mark scaler_sumr -big_split /=.
apply: eq_bigr=> i _.
rewrite !ffunE /= mulrDl.
change ((a * v i) * (fc_mark X i)%:R + w i * (fc_mark X i)%:R =
  a * (v i * (fc_mark X i)%:R) + w i * (fc_mark X i)%:R).
by rewrite mulrA.
Qed.

HB.instance Definition _ X := GRing.isLinear.Build R
  [the lmodType R of burnside_module] [the lmodType R of R^o] _
  (burnside_mark X) (burnside_mark_linear X).

Lemma burnside_mark_basis X a :
    burnside_mark X (burnside_basis a) = (fc_mark X a)%:R.
Proof.
rewrite /burnside_mark (bigD1 a) //= /burnside_basis ffunE eqxx mul1r.
rewrite big1 ?addr0 // => b /negbTE hb.
by rewrite ffunE eq_sym hb mul0r.
Qed.

Lemma burnside_basis_expansion (v : burnside_module) :
    v = \sum_a v a *: burnside_basis a.
Proof.
apply/ffunP=> b; rewrite sum_ffunE (bigD1 b) //=.
rewrite ffunE /burnside_basis ffunE eqxx.
rewrite burnside_regular_scale mulr1.
rewrite big1 ?addr0 // => a /negbTE ha.
rewrite ffunE /burnside_basis ffunE.
by rewrite burnside_regular_scale ha mulr0.
Qed.

Variable products : forall A B : fc_object C,
  @finite_product_decomposition (fc_category C) A B.

Definition burnside_basis_product (a b : fc_iso_class C) : burnside_module :=
  \sum_(i : fp_index (products (repr a) (repr b)))
    burnside_basis (fc_class (fp_apex (products (repr a) (repr b)) i)).

Definition burnside_mul (v w : burnside_module) : burnside_module :=
  \sum_a \sum_b (v a * w b) *: burnside_basis_product a b.

Lemma burnside_mark_basis_product X a b :
    burnside_mark X (burnside_basis_product a b) =
      (fc_mark X a)%:R * (fc_mark X b)%:R.
Proof.
rewrite /burnside_basis_product linear_sum /=.
under eq_bigr do rewrite burnside_mark_basis fc_mark_class.
rewrite -natr_sum -natrM /fc_mark.
congr (_%:R); exact: fc_product_cardinality.
Qed.

Theorem burnside_mark_mul X v w :
    burnside_mark X (burnside_mul v w) =
      burnside_mark X v * burnside_mark X w.
Proof.
rewrite /burnside_mul linear_sum /burnside_mark mulr_suml.
apply: eq_bigr=> a _; rewrite linear_sum mulr_sumr.
apply: eq_bigr=> b _.
rewrite linearZ /= burnside_mark_basis_product.
by rewrite burnside_regular_scale mulrACA.
Qed.

Lemma burnside_mul_addl u v w :
    burnside_mul (u + v) w = burnside_mul u w + burnside_mul v w.
Proof.
rewrite /burnside_mul -big_split /=; apply: eq_bigr=> a _.
rewrite -big_split /=; apply: eq_bigr=> b _.
by rewrite ffunE mulrDl scalerDl.
Qed.

Lemma burnside_mul_addr u v w :
    burnside_mul u (v + w) = burnside_mul u v + burnside_mul u w.
Proof.
rewrite /burnside_mul -big_split /=; apply: eq_bigr=> a _.
rewrite -big_split /=; apply: eq_bigr=> b _.
by rewrite ffunE mulrDr scalerDl.
Qed.

Lemma burnside_mul_scalel a v w :
    burnside_mul (a *: v) w = a *: burnside_mul v w.
Proof.
rewrite /burnside_mul scaler_sumr; apply: eq_bigr=> b _.
rewrite scaler_sumr; apply: eq_bigr=> c _.
by rewrite ffunE burnside_regular_scale scalerA mulrA.
Qed.

Lemma burnside_mul_scaler a v w :
    burnside_mul v (a *: w) = a *: burnside_mul v w.
Proof.
rewrite /burnside_mul scaler_sumr; apply: eq_bigr=> b _.
rewrite scaler_sumr; apply: eq_bigr=> c _.
by rewrite ffunE burnside_regular_scale scalerA mulrCA.
Qed.

Lemma burnside_left_mul_linear (v : burnside_module) :
    linear (burnside_mul v).
Proof.
move=> a w u; by rewrite burnside_mul_addr burnside_mul_scaler.
Qed.

HB.instance Definition _ (v : burnside_module) := GRing.isLinear.Build R
  [the lmodType R of burnside_module] [the lmodType R of burnside_module] _
  (burnside_mul v) (burnside_left_mul_linear v).

Lemma burnside_mul_basis a b :
    burnside_mul (burnside_basis a) (burnside_basis b) = burnside_basis_product a b.
Proof.
rewrite /burnside_mul (bigD1 a) //=.
have hz : \sum_(c | c != a) \sum_d
    (burnside_basis a c * burnside_basis b d) *: burnside_basis_product c d = 0.
  apply: big1=> c /negbTE hc; apply: big1=> d _.
  by rewrite /burnside_basis ffunE eq_sym hc mul0r scale0r.
rewrite hz addr0 (bigD1 b) //=.
rewrite /burnside_basis !ffunE !eqxx mul1r scale1r.
rewrite big1 ?addr0 // => d /negbTE hd.
by rewrite !ffunE eq_sym hd mul1r scale0r.
Qed.

End FreeBurnsideModule.

Print Assumptions burnside_mark_basis_product.
Print Assumptions burnside_mark_mul.
