From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryReindex CategoryIsomorphism BarPaths.
From DiazParkV16b Require Import SimplexCategory CategoryNerve SimplicialSet
  CategoryNervePathsPrefix CategoryNervePathsSplitting.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryNervePathEquivalence.
Import DPSimplexCategory DPCategoryNerve DPSimplicialSet DiazParkBarPaths
  DPCategoryNervePaths DPCategoryNerveSplitting.

Section NervePaths.
Variable C : category.

Fixpoint nerve_path_from (n : nat) :
    forall F : functor (ordinal_category n) C, @path_from C n (fobj F ord0) :=
  match n as k return forall F : functor (ordinal_category k) C,
      @path_from C k (fobj F ord0) with
  | 0 => fun _ => tt
  | S k => fun F => existT _ (fobj (nerve_tail F) ord0)
      (nerve_head_edge F, @nerve_path_from k (nerve_tail F))
  end.

Definition nerve_path n (F : functor (ordinal_category n) C) : @path C n :=
  existT _ (fobj F ord0) (nerve_path_from F).

Arguments nerve_path {_} _.

Definition path_cons n (x : C) (p : @path C n)
    (a : hom C x (path_source p)) : @path C n.+1 :=
  existT _ x (existT _ (path_source p) (a, projT2 p)).

Arguments path_cons {_} _ _ _.

Lemma nerve_path_step n (F : functor (ordinal_category n.+1) C) :
  nerve_path F = path_cons (fobj F ord0) (nerve_path (nerve_tail F))
    (nerve_head_edge F).
Proof. reflexivity. Qed.

Lemma path_cons_functor_congr n (x : C) (T U : functor (ordinal_category n) C)
    (e : T = U) (a : hom C x (fobj T ord0)) (b : hom C x (fobj U ord0)) :
  hom_transport (Logic.eq_refl x)
    (f_equal (fun F : functor (ordinal_category n) C => fobj F ord0) e) a = b ->
  path_cons x (nerve_path T) a = path_cons x (nerve_path U) b.
Proof. destruct e. cbn. intro h. subst b. reflexivity. Qed.

Lemma nerve_path_prefix n (x : C) (T : functor (ordinal_category n) C)
    (a : hom C x (fobj T ord0)) :
  nerve_path (nerve_prefix x T a) = path_cons x (nerve_path T) a.
Proof.
  rewrite nerve_path_step.
  apply (@path_cons_functor_congr n x _ T (@nerve_tail_prefix C n x T a)).
  rewrite hom_transport_loop. apply nerve_prefix_edge.
Qed.

Definition constant_nerve (x : C) (n : nat) : functor (ordinal_category n) C.
Proof.
  refine (@Build_functor (ordinal_category n) C (fun _ => x)
    (fun _ _ _ => identity x) _ _).
  - reflexivity.
  - intros. symmetry. apply compose_id_left.
Defined.

Lemma zero_vertex (i : 'I_1) : i = ord0.
Proof.
  destruct i as [[|i] hi].
  - apply val_inj. reflexivity.
  - discriminate hi.
Qed.

Lemma nerve_zero_split_object (F : functor (ordinal_category 0) C)
    (i : ordinal_category 0) :
  fobj (constant_nerve (fobj F ord0) 0) i = fobj F i.
Proof. rewrite (zero_vertex i). reflexivity. Defined.

Lemma nerve_zero_split (F : functor (ordinal_category 0) C) :
  constant_nerve (fobj F ord0) 0 = F.
Proof.
  refine (@functor_ext_pointwise _ _ _ _ (nerve_zero_split_object F) _).
  intros i j h. have ei := zero_vertex i. subst i.
  have ej := zero_vertex j. subst j.
  cbn. rewrite hom_transport_loop.
  replace h with (@identity (ordinal_category 0) ord0)
    by (cbn; apply Prop_irrelevance).
  symmetry. apply fmap_id.
Qed.

Lemma path_cons_drop_first n (x : C) (p : @path C n)
    (a : hom C x (path_source p)) :
  @path_drop_first C n (path_cons x p a) = p.
Proof. destruct p. reflexivity. Qed.

Lemma prefix_equal_of_paths n
    (IH : forall T U : functor (ordinal_category n) C,
      nerve_path T = nerve_path U -> T = U)
    (x y : C) (T U : functor (ordinal_category n) C)
    (a : hom C x (fobj T ord0)) (b : hom C y (fobj U ord0)) :
  path_cons x (nerve_path T) a = path_cons y (nerve_path U) b ->
    nerve_prefix x T a = nerve_prefix y U b.
Proof.
  intro e.
  have hTU : T = U.
  { apply IH. have h := f_equal (@path_drop_first C n) e.
    rewrite !path_cons_drop_first in h. exact h. }
  subst U.
  have hxy : x = y := f_equal (@path_source C n.+1) e.
  subst y.
  unfold path_cons in e.
  have e1 := @existT_inj2 [the eqType of classicType C]
    (fun x => @path_from C n.+1 x) x _ _ e.
  have e2 := @existT_inj2 [the eqType of classicType C]
    (fun z => (hom C x z * @path_from C n z)%type)
    (fobj T ord0) _ _ e1.
  have hab : a = b := f_equal (@fst _ _) e2.
  subst b. reflexivity.
Qed.

Lemma nerve_path_injective n :
  injective (@nerve_path n).
Proof.
  induction n as [|n IH]; intros F G h.
  - rewrite <- (nerve_zero_split F), <- (nerve_zero_split G).
    f_equal. exact (f_equal (@path_source C 0) h).
  - rewrite <- (nerve_prefix_split F), <- (nerve_prefix_split G).
    apply (prefix_equal_of_paths IH).
    rewrite <- !nerve_path_step. exact h.
Qed.

Lemma prefix_surjective_step n (p : @path C n)
    (T : functor (ordinal_category n) C) (e : nerve_path T = p)
    (x : C) (a : hom C x (path_source p)) :
  {F : functor (ordinal_category n.+1) C | nerve_path F = path_cons x p a}.
Proof.
  destruct e. exists (nerve_prefix x T a). apply nerve_path_prefix.
Defined.

Fixpoint nerve_path_surjective (n : nat) :
    forall p : @path C n, {F : functor (ordinal_category n) C | nerve_path F = p}.
Proof.
  destruct n as [|n].
  - intros [x []]. exists (constant_nerve x 0). reflexivity.
  - intros [x [y [a q]]].
    destruct (nerve_path_surjective n (existT _ y q)) as [T hT].
    exact (@prefix_surjective_step n (existT _ y q) T hT x a).
Defined.

Definition path_nerve n (p : @path C n) : functor (ordinal_category n) C :=
  proj1_sig (@nerve_path_surjective n p).

Arguments path_nerve {_} _.

Lemma nerve_path_nerve n (p : @path C n) : nerve_path (path_nerve p) = p.
Proof. exact (proj2_sig (@nerve_path_surjective n p)). Qed.

Lemma path_nerve_path n (F : functor (ordinal_category n) C) :
  path_nerve (nerve_path F) = F.
Proof. apply nerve_path_injective. apply nerve_path_nerve. Qed.

End NervePaths.
End DPCategoryNervePathEquivalence.
