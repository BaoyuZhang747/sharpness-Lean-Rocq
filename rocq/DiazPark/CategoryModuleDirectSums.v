(** Actual arbitrary dependent direct sums: finite-support families of
    arbitrary modules, with their universal linear map. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleProducts ModuleInfrastructure MackeyModuleCarriers BarFreeModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule.
Local Open Scope ring_scope.

Section DirectSum.
Variable R : pzRingType.
Variable I : Type.
Variable V : I -> lmodType R.
Definition sum_index := classicType I.
HB.instance Definition _ := Choice.on sum_index.

Definition sum_finite_support (v : module_product_type V) : Prop :=
  exists s : seq sum_index, forall i, i \notin s -> v i = 0.

Definition sum_support_subspace : module_subspace (module_product_type V).
Proof.
refine (@ModuleSubspace R (module_product_type V) sum_finite_support _ _ _).
- exists [::]; intros i hi; reflexivity.
- intros v w [s hs] [t ht]; exists (s ++ t).
  move=> i; rewrite mem_cat negb_or => /andP [hi hj].
  change (v i + w i = 0); rewrite hs // ht // addr0; reflexivity.
- intros a v [s hs]; exists s; intros i hi.
  change (a *: v i = 0); rewrite hs // scaler0; reflexivity.
Defined.

Definition module_sum_type : lmodType R :=
  [the lmodType R of submodule_carrier sum_support_subspace].

Definition sum_coefficient (v : module_sum_type) (i : I) : V i := submodule_val v i.
Lemma sum_coefficient_ext (v w : module_sum_type) :
  (forall i, sum_coefficient v i = sum_coefficient w i) -> v = w.
Proof. intro h; apply submodule_val_injective; apply functional_extensionality_dep; exact h. Qed.

Lemma sum_coefficient_linear i : linear (fun v => sum_coefficient v i).
Proof. intros a v w; reflexivity. Qed.
Definition sum_evaluation i (v : module_sum_type) : V i := sum_coefficient v i.
HB.instance Definition _ i := GRing.isLinear.Build R module_sum_type (V i) _
  (sum_evaluation i) (sum_coefficient_linear i).

Definition sum_support (v : module_sum_type) : seq sum_index :=
  undup (proj1_sig (constructive_indefinite_description (submodule_val_mem v))).
Lemma sum_support_uniq v : uniq (sum_support v).
Proof. exact: undup_uniq. Qed.
Lemma sum_coefficient_outside v i : i \notin sum_support v -> sum_coefficient v i = 0.
Proof.
rewrite /sum_support mem_undup.
exact: (proj2_sig (constructive_indefinite_description (submodule_val_mem v))).
Qed.

Definition sum_single_fun i (v : V i) j : V j :=
  match pselect (i = j) with
  | left h => eq_rect i (fun k => V k) v j h
  | right _ => 0
  end.

Lemma sum_single_fun_same i (v : V i) : sum_single_fun v i = v.
Proof.
unfold sum_single_fun; destruct (pselect (i = i)) as [h|h].
- replace h with (Logic.eq_refl i) by apply Prop_irrelevance; reflexivity.
- contradiction h; reflexivity.
Qed.
Lemma sum_single_fun_away i (v : V i) j : i <> j -> sum_single_fun v j = 0.
Proof. intro hij; unfold sum_single_fun; destruct (pselect (i = j)); [contradiction|reflexivity]. Qed.

Lemma sum_single_support i (v : V i) : sum_finite_support (sum_single_fun v).
Proof.
exists [:: i]; move=> j; rewrite in_cons in_nil orbF => hj.
apply sum_single_fun_away; intro h; subst j; move: hj; rewrite eqxx; discriminate.
Qed.

Definition sum_single i (v : V i) : module_sum_type :=
  @submodule_in R (module_product_type V) sum_support_subspace (sum_single_fun v) (sum_single_support v).

Lemma sum_single_same i (v : V i) : sum_coefficient (sum_single v) i = v.
Proof. exact: sum_single_fun_same. Qed.
Lemma sum_single_away i (v : V i) j : i <> j -> sum_coefficient (sum_single v) j = 0.
Proof. exact: sum_single_fun_away. Qed.

Lemma sum_single_linear i : linear (@sum_single i).
Proof.
intros a v w; apply sum_coefficient_ext; intro j.
change (sum_single_fun (a *: v + w) j = a *: sum_single_fun v j + sum_single_fun w j).
unfold sum_single_fun; destruct (pselect (i = j)) as [h|h].
- destruct h; reflexivity.
- rewrite scaler0 add0r; reflexivity.
Qed.
HB.instance Definition _ i := GRing.isLinear.Build R (V i) module_sum_type _
  (@sum_single i) (@sum_single_linear i).

Section Lift.
Variable W : lmodType R.
Variable f : forall i, {linear V i -> W}.

Definition sum_lift (v : module_sum_type) : W :=
  \sum_(i <- sum_support v) f i (sum_coefficient v i).

Lemma sum_lift_support v (s : seq sum_index) :
    uniq s -> (forall i, i \notin s -> sum_coefficient v i = 0) ->
    sum_lift v = \sum_(i <- s) f i (sum_coefficient v i).
Proof.
intros hs hv; unfold sum_lift; apply: sum_over_supports.
- exact: sum_support_uniq.
- exact hs.
- intros i hi; rewrite (sum_coefficient_outside hi) linear0; reflexivity.
- intros i hi; rewrite (hv i hi) linear0; reflexivity.
Qed.

Lemma sum_lift_linear : linear sum_lift.
Proof.
intros a v w.
pose s := undup (sum_support v ++ sum_support w).
have hs : uniq s := undup_uniq _.
have hv : forall i, i \notin s -> sum_coefficient v i = 0.
  move=> i; rewrite /s mem_undup mem_cat negb_or => /andP [hi _]; exact: sum_coefficient_outside.
have hw : forall i, i \notin s -> sum_coefficient w i = 0.
  move=> i; rewrite /s mem_undup mem_cat negb_or => /andP [_ hi]; exact: sum_coefficient_outside.
have hvw : forall i, i \notin s -> sum_coefficient (a *: v + w) i = 0.
  intros i hi; change (a *: sum_coefficient v i + sum_coefficient w i = 0).
  rewrite hv // hw // scaler0 addr0; reflexivity.
rewrite (sum_lift_support hs hvw) (sum_lift_support hs hv)
  (sum_lift_support hs hw) scaler_sumr -big_split.
apply eq_bigr; intros i hi; exact: linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R module_sum_type W _ sum_lift sum_lift_linear.

Lemma sum_lift_single i (v : V i) : sum_lift (sum_single v) = f i v.
Proof.
have hs : uniq ([:: i] : seq sum_index) by rewrite /=.
have hv : forall j : sum_index, j \notin ([:: i] : seq sum_index) -> sum_coefficient (sum_single v) j = 0.
  move=> j; rewrite in_cons in_nil orbF => hj.
  apply sum_single_away; intro h; subst j; move: hj; rewrite eqxx; discriminate.
rewrite (sum_lift_support hs hv) big_seq1 sum_single_same; reflexivity.
Qed.
End Lift.

Lemma sum_generation (v : module_sum_type) :
    \sum_(i <- sum_support v) sum_single (sum_coefficient v i) = v.
Proof.
apply sum_coefficient_ext; intro j.
change (sum_evaluation j (\sum_(i <- sum_support v) sum_single (sum_coefficient v i)) = sum_evaluation j v).
rewrite linear_sum /sum_evaluation.
case hj: (j \in sum_support v).
- rewrite (bigD1_seq (j : sum_index) hj (sum_support_uniq v)).
  change (sum_coefficient (sum_single (sum_coefficient v j)) j +
    \sum_(i <- sum_support v | i != j) sum_coefficient (sum_single (sum_coefficient v i)) j =
    sum_coefficient v j).
  rewrite sum_single_same.
  have hz : \sum_(i <- sum_support v | i != j)
      sum_coefficient (sum_single (sum_coefficient v i)) j = 0.
    apply big1; intros i hi; apply sum_single_away; exact: (elimN eqP hi).
  rewrite hz addr0; reflexivity.
- have hz : \sum_(i <- sum_support v)
      sum_coefficient (sum_single (sum_coefficient v i)) j = 0.
    apply big1_seq; intros i hi; apply sum_single_away; intro h; subst i; move: hi; rewrite hj; discriminate.
  rewrite hz; symmetry; apply sum_coefficient_outside; rewrite hj; reflexivity.
Qed.

Lemma sum_lift_unique (W : lmodType R) (f : forall i, {linear V i -> W})
    (g : {linear module_sum_type -> W}) :
    (forall i v, g (sum_single v) = f i v) -> forall v, g v = sum_lift f v.
Proof.
intros h v; rewrite -[in LHS](sum_generation v) linear_sum /sum_lift.
apply eq_bigr; intros i hi; exact: h.
Qed.
End DirectSum.

Arguments module_sum_type {R I} V.
Arguments sum_coefficient {R I V} v i.
Arguments sum_single {R I V i} v.







