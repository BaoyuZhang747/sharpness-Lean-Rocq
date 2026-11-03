From mathcomp Require Import all_ssreflect order boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplexSections.
Import DPSimplexCategory DPSimplexFactorization.

Lemma ordinal_section_monotone n m (f : ordinal_map n m)
    (g : 'I_m.+1 -> 'I_n.+1) (hg : forall y, f (g y) = y) :
  forall i j : 'I_m.+1, (i <= j)%N -> (g i <= g j)%N.
Proof.
  intros i j hij.
  have ht := leq_total (g i) (g j). move/orP: ht => [h|h]; first exact h.
  have hji := ordinal_monotone f h. rewrite !hg in hji.
  have ev : nat_of_ord i = nat_of_ord j.
  { apply/eqP. rewrite eqn_leq hij hji. reflexivity. }
  have e : i = j := val_inj ev. subst j. exact (leqnn (g i)).
Qed.

Definition section_function n m (f : ordinal_map n m) (hf : ordinal_surjective f)
    (y : 'I_m.+1) : 'I_n.+1 := proj1_sig (cid (hf y)).

Lemma section_function_right_inverse n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) y : f (section_function hf y) = y.
Proof. exact (proj2_sig (cid (hf y))). Qed.

Definition ordinal_section n m (f : ordinal_map n m) (hf : ordinal_surjective f) :
    ordinal_map m n.
Proof.
  refine (@OrdinalMap m n (@section_function n m f hf) _).
  apply (@ordinal_section_monotone n m f).
  exact (@section_function_right_inverse n m f hf).
Defined.

Arguments ordinal_section {_ _ _} _.

Lemma ordinal_section_right_inverse n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) :
  ordinal_map_compose (ordinal_section hf) f = ordinal_map_identity m.
Proof. apply ordinal_map_ext. exact (@section_function_right_inverse n m f hf). Qed.

Definition section_through_function n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) (x : 'I_n.+1) (y : 'I_m.+1) : 'I_n.+1 :=
  if y == f x then x else section_function hf y.

Lemma section_through_function_right_inverse n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) x y : f (section_through_function hf x y) = y.
Proof.
  unfold section_through_function. case: eqP => [e|e].
  - symmetry. exact e.
  - apply section_function_right_inverse.
Qed.

Definition ordinal_section_through n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) (x : 'I_n.+1) : ordinal_map m n.
Proof.
  refine (@OrdinalMap m n (@section_through_function n m f hf x) _).
  apply (@ordinal_section_monotone n m f).
  exact (@section_through_function_right_inverse n m f hf x).
Defined.

Arguments ordinal_section_through {_ _ _} _ _.

Lemma ordinal_section_through_right_inverse n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) x :
  ordinal_map_compose (ordinal_section_through hf x) f = ordinal_map_identity m.
Proof.
  apply ordinal_map_ext. exact (@section_through_function_right_inverse n m f hf x).
Qed.

Lemma ordinal_section_through_point n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) x : ordinal_section_through hf x (f x) = x.
Proof. change ((if f x == f x then x else section_function hf (f x)) = x). by rewrite eqxx. Qed.

Lemma ordinal_injective_dimension n m (f : ordinal_map n m) :
  ordinal_injective f -> (n <= m)%N.
Proof.
  intro hf. have h := leq_card f hf. rewrite !card_ord in h. exact h.
Qed.

Lemma ordinal_surjective_dimension n m (f : ordinal_map n m) :
  ordinal_surjective f -> (m <= n)%N.
Proof.
  intro hf. apply (@ordinal_injective_dimension m n (ordinal_section hf)).
  exact (@can_inj _ _ (@section_function n m f hf) f
    (@section_function_right_inverse n m f hf)).
Qed.

Lemma ordinal_injective_reflects_order n m (f : ordinal_map n m)
    (hf : ordinal_injective f) (i j : 'I_n.+1) :
  (f i <= f j)%N = (i <= j)%N.
Proof.
  apply/idP/idP; last exact (@ordinal_monotone n m f i j).
  intro hij. have ht := leq_total i j. move/orP: ht => [h|h]; first exact h.
  have hji := ordinal_monotone f h.
  have ev : nat_of_ord (f i) = nat_of_ord (f j).
  { apply/eqP. rewrite eqn_leq hij hji. reflexivity. }
  have e : i = j := hf i j (val_inj ev). subst j. exact (leqnn i).
Qed.

Lemma ordinal_injective_self_identity n (f : ordinal_map n n)
    (hf : ordinal_injective f) : f = ordinal_map_identity n.
Proof.
  apply ordinal_map_ext. intro i.
  exact (@Order.mono_unique _ [the finPOrderType _ of 'I_n.+1]
    [the finPOrderType _ of 'I_n.+1] f (fun x => x)
    (fun x y => leq_total x y) (leqnn _)
    (@ordinal_injective_reflects_order n n f hf)
    (fun _ _ => Logic.eq_refl _) i).
Qed.

Lemma ordinal_surjective_same_dimension_injective n m (f : ordinal_map n m)
    (hf : ordinal_surjective f) (e : n = m) : ordinal_injective f.
Proof.
  subst m. exact (@can_inj _ _ f (@section_function n n f hf)
    (canF_sym (@section_function_right_inverse n n f hf))).
Qed.

Lemma ordinal_surjective_self_identity n (f : ordinal_map n n)
    (hf : ordinal_surjective f) : f = ordinal_map_identity n.
Proof.
  apply ordinal_injective_self_identity.
  exact (@ordinal_surjective_same_dimension_injective n n f hf (Logic.eq_refl n)).
Qed.

End DPSimplexSections.
