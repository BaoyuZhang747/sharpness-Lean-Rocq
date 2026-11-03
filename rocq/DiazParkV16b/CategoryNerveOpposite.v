(** Actual reversal of functor simplices, with all face indices reversed. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryReindex CategoryIsomorphism.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators
  SimplicialSet SimplicialSetOperators CategoryNerve.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplexOperators DPSimplicialSet DPSimplicialOperators DPCategoryNerve.

Module DPCategoryNerveOpposite.
Lemma reverse_order n (i j : 'I_n.+1) : (i <= j)%N -> (rev_ord j <= rev_ord i)%N.
Proof. move=> h; change ((n - j <= n - i)%N); exact: leq_sub2l. Qed.

Lemma reverse_coface n (i : 'I_n.+2) (j : 'I_n.+1) :
  rev_ord (coface i j) = coface (rev_ord i) (rev_ord j).
Proof.
apply val_inj.
change (n.+2 - (coface_value i j).+1 = coface_value (n.+2 - i.+1) (n.+1 - j.+1)).
have hi : (val i < n.+2)%coq_nat := elimT ltP (ltn_ord i).
have hj : (val j < n.+1)%coq_nat := elimT ltP (ltn_ord j).
change (i < n.+2)%coq_nat in hi; change (j < n.+1)%coq_nat in hj.
rewrite !subSS /coface_value !subnE.
destruct (Nat.leb_spec0 i j); destruct (Nat.leb_spec0 (Nat.sub n.+1 i) (Nat.sub n j)); lia.
Qed.

Lemma opposite_transport (C : category) (x y x' y' : C) (ex : x = x') (ey : y = y')
    (h : hom C y x) :
  @hom_transport (opposite C) x y x' y' ex ey h = @hom_transport C y x y' x' ey ex h.
Proof. destruct ex, ey; reflexivity. Qed.

Lemma ordinal_fmap_transport (C : category) n (F : functor (ordinal_category n) C)
    (i j i' j' : ordinal_category n) (ei : i = i') (ej : j = j')
    (h : hom (ordinal_category n) i j) (k : hom (ordinal_category n) i' j') :
  hom_transport (f_equal (fobj F) ei) (f_equal (fobj F) ej) (fmap F h) = fmap F k.
Proof.
destruct ei, ej.
have eh : h = k by (cbn; apply Prop_irrelevance).
subst k; apply hom_transport_loop.
Qed.

Definition reverse_nerve (C : category) n (F : functor (ordinal_category n) C) :
    functor (ordinal_category n) (opposite C).
Proof.
refine (@Build_functor (ordinal_category n) (opposite C)
  (fun i => fobj F (rev_ord i)) (fun i j h => fmap F (reverse_order h)) _ _).
- move=> i; cbn; rewrite -fmap_id; f_equal; apply Prop_irrelevance.
- move=> i j k h g; cbn; rewrite -fmap_compose; f_equal; apply Prop_irrelevance.
Defined.

Definition unreverse_nerve (C : category) n (F : functor (ordinal_category n) (opposite C)) :
    functor (ordinal_category n) C.
Proof.
refine (@Build_functor (ordinal_category n) C
  (fun i => fobj F (rev_ord i)) (fun i j h => fmap F (reverse_order h)) _ _).
- move=> i; cbn.
  have e := fmap_id F (rev_ord i); cbn in e.
  rewrite -e; f_equal; apply Prop_irrelevance.
- move=> i j k h g; cbn.
  have e := fmap_compose F (reverse_order g) (reverse_order h); cbn in e.
  rewrite -e; f_equal; apply Prop_irrelevance.
Defined.

Lemma reverse_nerve_inverse (C : category) n (F : functor (ordinal_category n) C) :
  unreverse_nerve (reverse_nerve F) = F.
Proof.
refine (@functor_ext_pointwise (ordinal_category n) C (unreverse_nerve (reverse_nerve F)) F
  (fun i => f_equal (fobj F) (rev_ordK i)) _).
intros; cbn; apply ordinal_fmap_transport.
Qed.

Lemma unreverse_nerve_inverse (C : category) n (F : functor (ordinal_category n) (opposite C)) :
  reverse_nerve (unreverse_nerve F) = F.
Proof.
refine (@functor_ext_pointwise (ordinal_category n) (opposite C) (reverse_nerve (unreverse_nerve F)) F
  (fun i => f_equal (fobj F) (rev_ordK i)) _).
intros x y f.
exact (@ordinal_fmap_transport (opposite C) n F (rev_ord (rev_ord x)) (rev_ord (rev_ord y))
  x y (rev_ordK x) (rev_ordK y) (reverse_order (reverse_order f)) f).
Qed.

Lemma reverse_nerve_face (C : category) n (i : 'I_n.+2)
    (F : functor (ordinal_category n.+1) C) :
  reverse_nerve (face (nerve C) i F) = face (nerve (opposite C)) (rev_ord i) (reverse_nerve F).
Proof.
have e j : coface i (rev_ord j) = rev_ord (coface (rev_ord i) j).
  by rewrite reverse_coface rev_ordK.
refine (@functor_ext_pointwise (ordinal_category n) (opposite C)
  (reverse_nerve (face (nerve C) i F))
  (face (nerve (opposite C)) (rev_ord i) (reverse_nerve F))
  (fun j => f_equal (fobj F) (e j)) _).
intros; cbn; rewrite opposite_transport; apply ordinal_fmap_transport.
Qed.

Lemma unreverse_nerve_face (C : category) n (i : 'I_n.+2)
    (F : functor (ordinal_category n.+1) (opposite C)) :
  unreverse_nerve (face (nerve (opposite C)) i F) = face (nerve C) (rev_ord i) (unreverse_nerve F).
Proof.
apply (can_inj (@reverse_nerve_inverse C n)).
by rewrite reverse_nerve_face !unreverse_nerve_inverse rev_ordK.
Qed.
End DPCategoryNerveOpposite.












