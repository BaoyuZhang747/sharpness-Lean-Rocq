(** Directed-poset colimits of arbitrary modules.  The carrier below is the
    actual quotient of pairs (stage, element) by eventual equality. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp generic_quotient.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryLimits CategoryColimitMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Module DPFilteredLimits.

Record directed_poset := DirectedPoset {
  stage : Type;
  stage_le : stage -> stage -> Prop;
  stage_refl : forall i, stage_le i i;
  stage_trans : forall i j k, stage_le i j -> stage_le j k -> stage_le i k;
  stage_antisym : forall i j, stage_le i j -> stage_le j i -> i = j;
  stage_base : stage;
  stage_upper : forall i j, {k : stage | stage_le i k /\ stage_le j k}
}.
Arguments stage_le {_} _ _.
Arguments stage_refl {_} _.
Arguments stage_trans {_ _ _ _} _ _.
Arguments stage_antisym {_ _ _} _ _.
Arguments stage_base _.
Arguments stage_upper {_} _ _.

Definition upper {I : directed_poset} (i j : stage I) := proj1_sig (stage_upper i j).
Lemma le_upper_l {I : directed_poset} (i j : stage I) : stage_le i (upper i j).
Proof. exact (proj1 (proj2_sig (stage_upper i j))). Qed.
Lemma le_upper_r {I : directed_poset} (i j : stage I) : stage_le j (upper i j).
Proof. exact (proj2 (proj2_sig (stage_upper i j))). Qed.

Definition stage_category (I : directed_poset) : category.
Proof.
refine (@Build_category (stage I) (fun i j => stage_le i j)
  (@stage_refl I) (fun i j k f g => stage_trans f g) _ _ _);
  intros; apply Prop_irrelevance.
Defined.

Record directed_module (R : pzRingType) (I : directed_poset) := DirectedModule {
  dm_value : stage I -> lmodType R;
  dm_map : forall i j, stage_le i j -> {linear dm_value i -> dm_value j};
  dm_id : forall i (h : stage_le i i) x, dm_map h x = x;
  dm_comp : forall i j k (h : stage_le i j) (g : stage_le j k) x,
    dm_map g (dm_map h x) = dm_map (stage_trans h g) x
}.
Arguments dm_value {_ _} _ _.
Arguments dm_map {_ _} _ {_ _} _.
Arguments dm_id {_ _} _ {_} _ _.
Arguments dm_comp {_ _} _ {_ _ _} _ _ _.

Section Colimit.
Variable R : pzRingType.
Variable I : directed_poset.
Variable V : directed_module R I.

Lemma dm_proof_irrelevance i j (h g : stage_le i j) x :
    dm_map V h x = dm_map V g x.
Proof. by replace h with g by apply Prop_irrelevance. Qed.

Definition colimit_pair := classicType {i : stage I & dm_value V i}.
HB.instance Definition _ := Choice.on colimit_pair.

Definition pair_stage (x : colimit_pair) := projT1 x.
Definition pair_value (x : colimit_pair) : dm_value V (pair_stage x) := projT2 x.
Definition pair_at i (x : dm_value V i) : colimit_pair := existT _ i x.

Definition pair_equivalent (x y : colimit_pair) : Prop :=
  exists k (h : stage_le (pair_stage x) k) (g : stage_le (pair_stage y) k),
    dm_map V h (pair_value x) = dm_map V g (pair_value y).

Lemma pair_equivalent_refl x : pair_equivalent x x.
Proof. exists (pair_stage x), (stage_refl _), (stage_refl _); reflexivity. Qed.

Lemma pair_equivalent_sym x y : pair_equivalent x y -> pair_equivalent y x.
Proof. by move=> [k [h [g e]]]; exists k, g, h. Qed.

Lemma pair_equivalent_trans x y z :
    pair_equivalent x y -> pair_equivalent y z -> pair_equivalent x z.
Proof.
move=> [k [hx [hy he]]] [l [hy' [hz he']]].
pose m := upper k l.
have hk : stage_le k m := le_upper_l k l.
have hl : stage_le l m := le_upper_r k l.
exists m, (stage_trans hx hk), (stage_trans hz hl).
rewrite -(dm_comp V hx hk) -(dm_comp V hz hl) he -he'.
rewrite !dm_comp; exact: dm_proof_irrelevance.
Qed.

Definition pair_relation (x y : colimit_pair) := `[< pair_equivalent x y >].
Lemma pair_relation_refl : reflexive pair_relation.
Proof. move=> x; apply/asboolP; exact: pair_equivalent_refl. Qed.
Lemma pair_relation_sym : symmetric pair_relation.
Proof. move=> x y; apply/asboolP/asboolP; exact: pair_equivalent_sym. Qed.
Lemma pair_relation_trans : transitive pair_relation.
Proof.
move=> x y z /asboolP h /asboolP g; apply/asboolP.
exact: pair_equivalent_trans h g.
Qed.
Definition pair_equivalence :=
  EquivRel pair_relation pair_relation_refl pair_relation_sym pair_relation_trans.
Definition directed_colimit := {eq_quot pair_equivalence}.
HB.instance Definition _ := [Choice of directed_colimit by <:%/].

Definition colimit_class (x : colimit_pair) : directed_colimit :=
  \pi_(directed_colimit) x.
Definition colimit_in i (x : dm_value V i) := colimit_class (pair_at x).

Lemma colimit_class_eq x y :
    colimit_class x = colimit_class y <-> pair_equivalent x y.
Proof.
have hp : reflect (colimit_class x = colimit_class y) (pair_relation x y).
  exact: eqmodP.
split.
- move=> /hp h; exact (elimT (asboolP _) h).
- move=> h; apply/hp; apply/asboolP; exact h.
Qed.

Lemma colimit_class_repr x : colimit_class (repr x) = x.
Proof. exact: reprK. Qed.

Lemma colimit_in_eq i j (x : dm_value V i) (y : dm_value V j) :
    colimit_in x = colimit_in y <->
    exists k (h : stage_le i k) (g : stage_le j k), dm_map V h x = dm_map V g y.
Proof. exact: colimit_class_eq. Qed.

Lemma colimit_in_map i j (h : stage_le i j) (x : dm_value V i) :
    colimit_in (dm_map V h x) = colimit_in x.
Proof.
apply/colimit_in_eq; exists j, (stage_refl j), h; rewrite dm_id; reflexivity.
Qed.

Lemma colimit_in_surjective (x : directed_colimit) :
    exists i (v : dm_value V i), colimit_in v = x.
Proof.
exists (pair_stage (repr x)), (pair_value (repr x)).
change (colimit_class (existT _ (projT1 (repr x)) (projT2 (repr x))) = x).
have he : existT (fun i => dm_value V i) (projT1 (repr x)) (projT2 (repr x)) = repr x.
  case (repr x); reflexivity.
rewrite he; exact: colimit_class_repr.
Qed.

Definition colimit_zero : directed_colimit := colimit_in (0 : dm_value V (stage_base I)).
Definition colimit_opp (x : directed_colimit) : directed_colimit :=
  colimit_in (- pair_value (repr x)).
Definition colimit_scale (a : R) (x : directed_colimit) : directed_colimit :=
  colimit_in (a *: pair_value (repr x)).
Definition pair_add (x y : colimit_pair) : colimit_pair :=
  pair_at (dm_map V (le_upper_l (pair_stage x) (pair_stage y)) (pair_value x) +
    dm_map V (le_upper_r (pair_stage x) (pair_stage y)) (pair_value y)).
Definition colimit_add (x y : directed_colimit) : directed_colimit :=
  colimit_class (pair_add (repr x) (repr y)).

Lemma class_pair_add_upper x y k (hx : stage_le (pair_stage x) k)
    (hy : stage_le (pair_stage y) k) :
    colimit_class (pair_add x y) =
    colimit_in (dm_map V hx (pair_value x) + dm_map V hy (pair_value y)).
Proof.
apply/colimit_class_eq.
pose u := upper (pair_stage x) (pair_stage y).
pose t := upper u k.
have hu : stage_le u t := le_upper_l u k.
have hk : stage_le k t := le_upper_r u k.
exists t, hu, hk.
change (dm_map V hu (dm_map V (le_upper_l _ _) (pair_value x) +
  dm_map V (le_upper_r _ _) (pair_value y)) =
  dm_map V hk (dm_map V hx (pair_value x) + dm_map V hy (pair_value y))).
rewrite !linearD !dm_comp.
f_equal; exact: dm_proof_irrelevance.
Qed.

Lemma pair_add_compatible x x' y y' :
    pair_equivalent x x' -> pair_equivalent y y' ->
    colimit_class (pair_add x y) = colimit_class (pair_add x' y').
Proof.
move=> [k [hx [hx' he]]] [l [hy [hy' he']]].
pose t := upper k l.
have hk : stage_le k t := le_upper_l k l.
have hl : stage_le l t := le_upper_r k l.
rewrite (class_pair_add_upper (x := x) (y := y) (stage_trans hx hk) (stage_trans hy hl)).
rewrite (class_pair_add_upper (x := x') (y := y') (stage_trans hx' hk) (stage_trans hy' hl)).
rewrite -!dm_comp he he'; reflexivity.
Qed.

Lemma colimit_add_in i j (x : dm_value V i) (y : dm_value V j) k
    (h : stage_le i k) (g : stage_le j k) :
    colimit_add (colimit_in x) (colimit_in y) = colimit_in (dm_map V h x + dm_map V g y).
Proof.
rewrite /colimit_add.
transitivity (colimit_class (pair_add (pair_at x) (pair_at y))).
- apply pair_add_compatible; apply/colimit_class_eq; exact: colimit_class_repr.
- exact: class_pair_add_upper.
Qed.

Lemma colimit_opp_in i (x : dm_value V i) :
    colimit_opp (colimit_in x) = colimit_in (-x).
Proof.
have [k [h [g he]]] : pair_equivalent (repr (colimit_in x)) (pair_at x).
  apply/colimit_class_eq; exact: colimit_class_repr.
apply/colimit_in_eq; exists k, h, g.
rewrite !linearN he; reflexivity.
Qed.

Lemma colimit_scale_in a i (x : dm_value V i) :
    colimit_scale a (colimit_in x) = colimit_in (a *: x).
Proof.
have [k [h [g he]]] : pair_equivalent (repr (colimit_in x)) (pair_at x).
  apply/colimit_class_eq; exact: colimit_class_repr.
apply/colimit_in_eq; exists k, h, g.
rewrite !linearZ he; reflexivity.
Qed.

Lemma colimit_zero_in i : colimit_in (0 : dm_value V i) = colimit_zero.
Proof.
apply/colimit_in_eq.
exists (upper i (stage_base I)), (le_upper_l _ _), (le_upper_r _ _).
rewrite !linear0; reflexivity.
Qed.

Lemma colimit_add_same i (x y : dm_value V i) :
    colimit_add (colimit_in x) (colimit_in y) = colimit_in (x + y).
Proof. rewrite (colimit_add_in x y (stage_refl i) (stage_refl i)) !dm_id; reflexivity. Qed.

Lemma colimit_joint2 (x y : directed_colimit) :
    exists i (a b : dm_value V i), colimit_in a = x /\ colimit_in b = y.
Proof.
have [i [a <-]] := colimit_in_surjective x.
have [j [b <-]] := colimit_in_surjective y.
exists (upper i j), (dm_map V (le_upper_l i j) a), (dm_map V (le_upper_r i j) b).
split; exact: colimit_in_map.
Qed.

Lemma colimit_joint3 (x y z : directed_colimit) :
    exists i (a b c : dm_value V i),
      colimit_in a = x /\ colimit_in b = y /\ colimit_in c = z.
Proof.
have [i [a [b [<- <-]]]] := colimit_joint2 x y.
have [j [c <-]] := colimit_in_surjective z.
exists (upper i j), (dm_map V (le_upper_l i j) a),
  (dm_map V (le_upper_l i j) b), (dm_map V (le_upper_r i j) c).
split; [exact: colimit_in_map | split; exact: colimit_in_map].
Qed.

Lemma colimit_addA : associative colimit_add.
Proof.
move=> x y z; have [i [a [b [c [<- [<- <-]]]]]] := colimit_joint3 x y z.
rewrite !colimit_add_same addrA; reflexivity.
Qed.
Lemma colimit_addC : commutative colimit_add.
Proof.
move=> x y; have [i [a [b [<- <-]]]] := colimit_joint2 x y.
rewrite !colimit_add_same addrC; reflexivity.
Qed.
Lemma colimit_add0 : left_id colimit_zero colimit_add.
Proof.
move=> x; have [i [a <-]] := colimit_in_surjective x.
rewrite -(colimit_zero_in i) colimit_add_same add0r; reflexivity.
Qed.
Lemma colimit_addN : left_inverse colimit_zero colimit_opp colimit_add.
Proof.
move=> x; have [i [a <-]] := colimit_in_surjective x.
rewrite colimit_opp_in colimit_add_same addNr; exact: colimit_zero_in.
Qed.
HB.instance Definition _ := GRing.isZmodule.Build directed_colimit
  colimit_addA colimit_addC colimit_add0 colimit_addN.

Lemma colimit_scaleA a b x :
    colimit_scale a (colimit_scale b x) = colimit_scale (a * b) x.
Proof.
have [i [v <-]] := colimit_in_surjective x.
rewrite !colimit_scale_in scalerA; reflexivity.
Qed.
Lemma colimit_scale1 : left_id 1 colimit_scale.
Proof.
move=> x; have [i [v <-]] := colimit_in_surjective x.
rewrite colimit_scale_in scale1r; reflexivity.
Qed.
Lemma colimit_scaleDr : right_distributive colimit_scale +%R.
Proof.
move=> a x y; have [i [u [v [<- <-]]]] := colimit_joint2 x y.
change (colimit_scale a (colimit_add (colimit_in u) (colimit_in v)) =
  colimit_add (colimit_scale a (colimit_in u)) (colimit_scale a (colimit_in v))).
rewrite colimit_add_same !colimit_scale_in colimit_add_same scalerDr; reflexivity.
Qed.
Lemma colimit_scaleDl x a b :
    colimit_scale (a + b) x = colimit_scale a x + colimit_scale b x.
Proof.
have [i [v <-]] := colimit_in_surjective x.
change (colimit_scale (a + b) (colimit_in v) =
  colimit_add (colimit_scale a (colimit_in v)) (colimit_scale b (colimit_in v))).
rewrite !colimit_scale_in colimit_add_same scalerDl; reflexivity.
Qed.
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R directed_colimit
  colimit_scaleA colimit_scale1 colimit_scaleDr colimit_scaleDl.

Definition colimit_module : lmodType R := [the lmodType R of directed_colimit].

Lemma colimit_in_linear i : linear (@colimit_in i).
Proof.
move=> a x y; change (colimit_in (a *: x + y) =
  colimit_add (colimit_scale a (colimit_in x)) (colimit_in y)).
rewrite colimit_scale_in colimit_add_same; reflexivity.
Qed.
HB.instance Definition _ i := GRing.isLinear.Build R (dm_value V i)
  directed_colimit _ (@colimit_in i) (@colimit_in_linear i).

Lemma colimit_in_zero i (x : dm_value V i) :
    colimit_in x = 0 <-> exists j (h : stage_le i j), dm_map V h x = 0.
Proof.
split.
- move=> hx.
  have he : colimit_in x = colimit_in (0 : dm_value V i).
    rewrite colimit_zero_in; exact hx.
  have [j [h [g e]]] := (proj1 (colimit_in_eq x 0) he).
  exists j, h; by rewrite linear0 in e.
- move=> [j [h e]].
  rewrite -(colimit_in_map h x) e; exact: colimit_zero_in.
Qed.

Definition module_system_functor : functor (stage_category I) (module_category R).
Proof.
refine (@Build_functor (stage_category I) (module_category R) (dm_value V)
  (fun i j h => module_hom_of_linear (dm_map V h)) _ _).
- move=> i; apply module_hom_ext=> x; exact: dm_id.
- move=> i j k h g; apply module_hom_ext=> x; symmetry; exact: dm_comp.
Defined.

Definition module_colimit_cocone : cocone module_system_functor colimit_module.
Proof.
refine (@Build_cocone (stage_category I) (module_category R) module_system_functor
  colimit_module (fun i => module_hom_of_linear (@colimit_in i)) _).
move=> i j h; apply module_hom_ext=> x; exact: colimit_in_map.
Defined.

Section Universal.
Variable W : lmodType R.
Variable f : forall i, {linear dm_value V i -> W}.
Hypothesis f_compatible : forall i j (h : stage_le i j) x, f j (dm_map V h x) = f i x.

Definition colimit_lift (x : directed_colimit) : W :=
  f (pair_stage (repr x)) (pair_value (repr x)).

Lemma colimit_lift_in i (x : dm_value V i) : colimit_lift (colimit_in x) = f i x.
Proof.
have [k [h [g he]]] : pair_equivalent (repr (colimit_in x)) (pair_at x).
  apply/colimit_class_eq; exact: colimit_class_repr.
rewrite /colimit_lift -(f_compatible h) -(f_compatible g) he; reflexivity.
Qed.

Lemma colimit_lift_linear : linear colimit_lift.
Proof.
move=> a x y; have [i [u [v [<- <-]]]] := colimit_joint2 x y.
change (colimit_lift (colimit_add (colimit_scale a (colimit_in u)) (colimit_in v)) =
  a *: colimit_lift (colimit_in u) + colimit_lift (colimit_in v)).
rewrite colimit_scale_in colimit_add_same !colimit_lift_in; exact: linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R directed_colimit W _
  colimit_lift colimit_lift_linear.

Lemma colimit_lift_unique (g : {linear directed_colimit -> W}) :
    (forall i x, g (colimit_in x) = f i x) -> forall x, g x = colimit_lift x.
Proof.
move=> hg x; have [i [v <-]] := colimit_in_surjective x.
rewrite hg colimit_lift_in; reflexivity.
Qed.
End Universal.

Definition module_colimit_desc (W : lmodType R)
    (s : cocone module_system_functor W) : module_hom colimit_module W.
Proof.
exact (exist _ (colimit_lift (fun i => module_hom_to_linear (cocone_leg s i)))
  (@colimit_lift_linear W (fun i => module_hom_to_linear (cocone_leg s i))
    (fun i j h x => congr1 (fun k => module_hom_fun k x) (cocone_natural s h)))).
Defined.

Lemma module_colimit_desc_in W (s : cocone module_system_functor W) i
    (x : dm_value V i) : module_colimit_desc s (colimit_in x) = module_hom_fun (cocone_leg s i) x.
Proof.
change (colimit_lift (fun j => module_hom_to_linear (cocone_leg s j)) (colimit_in x) =
  module_hom_to_linear (cocone_leg s i) x).
apply colimit_lift_in => j k h y.
exact (congr1 (fun f => module_hom_fun f y) (cocone_natural s h)).
Qed.

Definition module_colimit : colimiting_cocone module_system_functor.
Proof.
refine (@Build_colimiting_cocone (stage_category I) (module_category R)
  module_system_functor colimit_module module_colimit_cocone (@module_colimit_desc) _ _).
- move=> W s i; apply module_hom_ext=> x; exact: module_colimit_desc_in.
- move=> W s g hg; apply module_hom_ext=> x.
  have [i [v <-]] := colimit_in_surjective x.
  rewrite module_colimit_desc_in.
  exact (congr1 (fun k => module_hom_fun k v) (hg i)).
Defined.

End Colimit.
End DPFilteredLimits.
