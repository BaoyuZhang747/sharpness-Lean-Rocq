From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplexCategory.

(** Object n is the nonempty finite ordinal [n], with n+1 vertices.
    Every weakly monotone function is a morphism, including noninjective ones. *)
Record ordinal_map (n m : nat) := OrdinalMap {
  ordinal_function :> 'I_n.+1 -> 'I_m.+1;
  ordinal_monotone : forall i j : 'I_n.+1, (i <= j)%N ->
    (ordinal_function i <= ordinal_function j)%N
}.

Arguments ordinal_function {_ _} _ _.
Arguments ordinal_monotone {_ _} _ {_ _} _.

Lemma ordinal_map_ext n m (f g : ordinal_map n m) :
  (forall i, f i = g i) -> f = g.
Proof.
  destruct f as [f hf], g as [g hg]; simpl.
  intro h. assert (e : f = g).
  { apply functional_extensionality_dep. exact h. }
  destruct e. f_equal. apply Prop_irrelevance.
Qed.

Definition ordinal_map_identity n : ordinal_map n n.
Proof.
  refine (@OrdinalMap n n (fun i => i) _).
  intros i j hij. exact hij.
Defined.

Definition ordinal_map_compose n m k (f : ordinal_map n m)
    (g : ordinal_map m k) : ordinal_map n k.
Proof.
  refine (@OrdinalMap n k (fun i => g (f i)) _).
  intros i j hij. apply ordinal_monotone. exact (ordinal_monotone f hij).
Defined.

Arguments ordinal_map_compose {_ _ _} _ _.

Lemma ordinal_map_identity_apply n (i : 'I_n.+1) :
  ordinal_map_identity n i = i.
Proof. reflexivity. Qed.

Lemma ordinal_map_compose_apply n m k (f : ordinal_map n m)
    (g : ordinal_map m k) i : ordinal_map_compose f g i = g (f i).
Proof. reflexivity. Qed.

Definition simplex_category : category.
Proof.
  refine (@Build_category nat ordinal_map ordinal_map_identity
    (@ordinal_map_compose) _ _ _).
  - intros n m f. apply ordinal_map_ext. intro i. reflexivity.
  - intros n m f. apply ordinal_map_ext. intro i. reflexivity.
  - intros n m k l f g h. apply ordinal_map_ext. intro i. reflexivity.
Defined.

(** The linearly ordered category [n] itself, used to define its nerve
    without limiting the action to generators of the simplex category. *)
Definition ordinal_category (n : nat) : category.
Proof.
  refine (@Build_category 'I_n.+1 (fun i j => (i <= j)%N)
    (fun i => leqnn i) (fun i j k hij hjk => leq_trans hij hjk) _ _ _);
    intros; apply Prop_irrelevance.
Defined.

Definition ordinal_functor n m (f : ordinal_map n m) :
    functor (ordinal_category n) (ordinal_category m).
Proof.
  refine (@Build_functor (ordinal_category n) (ordinal_category m) f
    (fun i j hij => ordinal_monotone f hij) _ _);
    intros; cbn; apply Prop_irrelevance.
Defined.

Arguments ordinal_functor {_ _} _.

Lemma ordinal_functor_identity n :
  ordinal_functor (ordinal_map_identity n) = functor_id (ordinal_category n).
Proof.
  refine (@functor_ext_pointwise _ _
    (ordinal_functor (ordinal_map_identity n))
    (functor_id (ordinal_category n)) (fun _ => Logic.eq_refl _) _).
  intros. cbn. apply Prop_irrelevance.
Qed.

Lemma ordinal_functor_compose n m k (f : ordinal_map n m)
    (g : ordinal_map m k) :
  ordinal_functor (ordinal_map_compose f g) =
    functor_comp (ordinal_functor f) (ordinal_functor g).
Proof.
  refine (@functor_ext_pointwise _ _
    (ordinal_functor (ordinal_map_compose f g))
    (functor_comp (ordinal_functor f) (ordinal_functor g))
    (fun _ => Logic.eq_refl _) _).
  intros. cbn. apply Prop_irrelevance.
Qed.

End DPSimplexCategory.
