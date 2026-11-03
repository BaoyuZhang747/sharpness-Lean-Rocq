From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import CategoryModuleProducts ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Finite-support coefficient functions on an arbitrary type.  The ring may
    be noncommutative or the zero ring; the generating type is unrestricted. *)
Module DiazParkFreeModule.

Section SupportedSums.
Variable I : eqType.
Variable V : zmodType.

Lemma sum_over_supports (F : I -> V) (s t : seq I) :
  uniq s -> uniq t ->
  (forall x, x \notin s -> F x = 0) ->
  (forall x, x \notin t -> F x = 0) ->
  \sum_(x <- s) F x = \sum_(x <- t) F x.
Proof.
move=> hs ht hFs hFt.
have hs0 : \sum_(x <- s | x \notin t) F x = 0.
  by apply: big1 => x hx; exact: hFt hx.
have ht0 : \sum_(x <- t | x \notin s) F x = 0.
  by apply: big1 => x hx; exact: hFs hx.
rewrite (bigID (mem t)) /= hs0 addr0.
rewrite [RHS](bigID (mem s)) /= ht0 addr0.
rewrite -[in LHS]big_filter -[in RHS]big_filter.
apply: perm_big; apply: uniq_perm.
- exact: filter_uniq hs.
- exact: filter_uniq ht.
- by move=> x; rewrite !mem_filter andbC.
Qed.

End SupportedSums.

Section FreeModule.
Variable R : pzRingType.
Variable X : Type.

Definition generator_type := classicType X.
HB.instance Definition _ := Choice.on generator_type.

Definition coefficient_product : lmodType R :=
  module_product_type (fun _ : generator_type => [the lmodType R of R^o]).

Definition has_finite_support (a : coefficient_product) : Prop :=
  exists s : seq generator_type, forall x, x \notin s -> a x = 0.

Definition finite_support_subspace : module_subspace coefficient_product.
Proof.
refine (@ModuleSubspace R coefficient_product has_finite_support _ _ _).
- exists [::]; by move=> x hx.
- move=> a b [s hs] [t ht]; exists (s ++ t).
  move=> x; rewrite mem_cat negb_or => /andP [hx hy].
  change (a x + b x = 0); by rewrite hs // ht // addr0.
- move=> r a [s hs]; exists s; move=> x hx.
  change (r * a x = 0); by rewrite hs // mulr0.
Defined.

Definition free_module : lmodType R :=
  [the lmodType R of submodule_carrier finite_support_subspace].

Definition free_coefficient (a : free_module) (x : generator_type) : R^o :=
  submodule_val a x.

Lemma free_coefficient_ext (a b : free_module) :
  (forall x, free_coefficient a x = free_coefficient b x) -> a = b.
Proof.
move=> h; apply submodule_val_injective.
apply functional_extensionality_dep; exact: h.
Qed.

Lemma free_coefficient_linear x : linear (fun a => free_coefficient a x).
Proof. by move=> r a b. Qed.

Definition free_support (a : free_module) : seq generator_type :=
  undup (proj1_sig (constructive_indefinite_description (submodule_val_mem a))).

Lemma free_support_uniq (a : free_module) : uniq (free_support a).
Proof. exact: undup_uniq. Qed.

Lemma free_coefficient_outside (a : free_module) x :
  x \notin free_support a -> free_coefficient a x = 0.
Proof.
rewrite /free_support mem_undup.
exact: (proj2_sig (constructive_indefinite_description (submodule_val_mem a))).
Qed.

Definition free_basis_fun (x : generator_type) : coefficient_product :=
  fun y => if x == y then 1 else 0.

Lemma free_basis_support (x : generator_type) : has_finite_support (free_basis_fun x).
Proof.
exists [:: x]; move=> y.
rewrite in_cons in_nil orbF => hy.
by rewrite /free_basis_fun eq_sym (negbTE hy).
Qed.

Definition free_basis (x : generator_type) : free_module :=
  @submodule_in R coefficient_product finite_support_subspace
    (free_basis_fun x) (free_basis_support x).

Lemma free_basis_coefficient x y :
  free_coefficient (free_basis x) y = if x == y then 1 else 0.
Proof. reflexivity. Qed.

Section Lift.
Variable V : lmodType R.
Variable f : generator_type -> V.

Definition free_lift (a : free_module) : V :=
  \sum_(x <- free_support a) (free_coefficient a x : R) *: f x.

Lemma free_lift_support (a : free_module) (s : seq generator_type) :
  uniq s -> (forall x, x \notin s -> free_coefficient a x = 0) ->
  free_lift a = \sum_(x <- s) (free_coefficient a x : R) *: f x.
Proof.
move=> hs ha; apply: sum_over_supports => //.
- exact: free_support_uniq.
- by move=> x hx; rewrite (free_coefficient_outside hx) scale0r.
- by move=> x hx; rewrite (ha x hx) scale0r.
Qed.

Lemma free_lift_linear : linear free_lift.
Proof.
move=> r a b.
pose s := undup (free_support a ++ free_support b).
have hs : uniq s := undup_uniq _.
have ha : forall x, x \notin s -> free_coefficient a x = 0.
  move=> x; rewrite /s mem_undup mem_cat negb_or => /andP [hx _].
  exact: free_coefficient_outside hx.
have hb : forall x, x \notin s -> free_coefficient b x = 0.
  move=> x; rewrite /s mem_undup mem_cat negb_or => /andP [_ hx].
  exact: free_coefficient_outside hx.
have hab : forall x, x \notin s -> free_coefficient (r *: a + b) x = 0.
  move=> x hx.
  change (r * free_coefficient a x + free_coefficient b x = 0).
  by rewrite ha // hb // mulr0 addr0.
rewrite (free_lift_support hs hab) (free_lift_support hs ha)
  (free_lift_support hs hb) scaler_sumr -big_split.
apply: eq_bigr => x _.
change ((r * free_coefficient a x + free_coefficient b x) *: f x =
  r *: ((free_coefficient a x : R) *: f x) + (free_coefficient b x : R) *: f x).
by rewrite scalerDl scalerA.
Qed.

HB.instance Definition _ :=
  GRing.isLinear.Build R free_module V _ free_lift free_lift_linear.

Lemma free_lift_basis x : free_lift (free_basis x) = f x.
Proof.
have hx : uniq [:: x] by rewrite /=.
have hb : forall y, y \notin [:: x] -> free_coefficient (free_basis x) y = 0.
  move=> y; rewrite in_cons in_nil orbF => hy.
  by rewrite free_basis_coefficient eq_sym (negbTE hy).
by rewrite (free_lift_support hx hb) big_seq1 free_basis_coefficient eqxx scale1r.
Qed.

End Lift.

Definition free_evaluation_fun (x : generator_type) (a : free_module) : R^o :=
  free_coefficient a x.

Lemma free_evaluation_linear x : linear (free_evaluation_fun x).
Proof. exact: free_coefficient_linear. Qed.

HB.instance Definition _ x :=
  GRing.isLinear.Build R free_module [the lmodType R of R^o] _
    (free_evaluation_fun x) (free_evaluation_linear x).

Lemma free_basis_generation (a : free_module) :
  \sum_(y <- free_support a) (free_coefficient a y : R) *: free_basis y = a.
Proof.
apply free_coefficient_ext => x.
change (free_evaluation_fun x
  (\sum_(y <- free_support a) (free_coefficient a y : R) *: free_basis y) =
  free_evaluation_fun x a).
rewrite linear_sum.
case hx: (x \in free_support a).
- rewrite (bigD1_seq x hx (free_support_uniq a)).
  have hz : \sum_(y <- free_support a | y != x)
      free_evaluation_fun x ((free_coefficient a y : R) *: free_basis y) = 0.
    apply: big1 => y hy.
    by rewrite linearZ /= /free_basis_fun (negbTE hy) scaler0.
  rewrite hz.
  change (free_evaluation_fun x ((free_coefficient a x : R) *: free_basis x) + 0 =
    free_evaluation_fun x a).
  rewrite addr0 linearZ /= /free_basis_fun eqxx.
  exact: mulr1.
- have hz : \sum_(y <- free_support a)
      free_evaluation_fun x ((free_coefficient a y : R) *: free_basis y) = 0.
    apply: big1_seq => y hy.
    have hyx : y != x by apply/eqP => hyx; move: hy; rewrite hyx hx.
    by rewrite linearZ /= /free_basis_fun (negbTE hyx) scaler0.
  rewrite hz /free_evaluation_fun.
  symmetry; apply free_coefficient_outside; by rewrite hx.
Qed.

Lemma free_lift_unique (V : lmodType R) (f : generator_type -> V)
    (g : {linear free_module -> V}) :
  (forall x, g (free_basis x) = f x) -> forall a, g a = free_lift f a.
Proof.
move=> h a; rewrite -[in LHS](free_basis_generation a) linear_sum /free_lift.
apply: eq_bigr => x _; by rewrite linearZ h.
Qed.

Lemma free_lift_ext (V : lmodType R) (g h : {linear free_module -> V}) :
  (forall x, g (free_basis x) = h (free_basis x)) -> forall a, g a = h a.
Proof.
move=> e a.
rewrite (free_lift_unique e).
symmetry; apply free_lift_unique; reflexivity.
Qed.

End FreeModule.

Section FreeMaps.
Variable R : pzRingType.

Definition free_map (X Y : Type) (f : X -> Y) :
    {linear free_module R X -> free_module R Y} :=
  (free_lift (fun x => free_basis R (f x)) :
    {linear free_module R X -> free_module R Y}).

Arguments free_map {X Y} f.

Lemma free_map_basis (X Y : Type) (f : X -> Y) x :
  free_map f (free_basis R x) = free_basis R (f x).
Proof. exact: free_lift_basis. Qed.

Variables X Y Z : Type.

Lemma free_map_composition (f : X -> Y) (g : Y -> Z) (a : free_module R X) :
  free_map (g \o f) a = free_map g (free_map f a).
Proof.
apply: (free_lift_ext (g := free_map (g \o f))
  (h := (free_map g \o free_map f : {linear free_module R X -> free_module R Z}))).
by move=> x; rewrite /= !free_map_basis.
Qed.

End FreeMaps.

Lemma free_map_identity (R : pzRingType) (X : Type) (a : free_module R X) :
  free_map R (@idfun X) a = a.
Proof.
apply: (free_lift_ext (g := free_map R (@idfun X))
  (h := (idfun : {linear free_module R X -> free_module R X}))).
by move=> x; rewrite free_map_basis.
Qed.

Section Projectivity.
Variable R : pzRingType.
Variable X : Type.
Variables V W : lmodType R.
Variable q : {linear V -> W}.
Hypothesis q_surjective : forall w, exists v, q v = w.

Theorem free_module_lift_surjection (f : {linear free_module R X -> W}) :
  exists g : {linear free_module R X -> V}, forall a, q (g a) = f a.
Proof.
pose v := fun x : X => proj1_sig
  (constructive_indefinite_description (q_surjective (f (free_basis R x)))).
exists (free_lift v : {linear free_module R X -> V}).
apply: (free_lift_ext
  (g := (q \o free_lift v : {linear free_module R X -> W})) (h := f)).
move=> x; rewrite /= free_lift_basis /v.
exact: (proj2_sig (constructive_indefinite_description
  (q_surjective (f (free_basis R x))))).
Qed.

End Projectivity.
End DiazParkFreeModule.
