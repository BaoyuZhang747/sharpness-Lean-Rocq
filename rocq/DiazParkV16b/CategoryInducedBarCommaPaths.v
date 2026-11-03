(** The induced bar basis is exactly the ordinary strings of the actual
    structured comma d-downarrow-q. *)
From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryComma CategoryStructured BarPaths.
From DiazParkV16b Require Import CategoryBarPullbackPaths CategoryInducedBarTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkBarPaths DPCategoryBarPullback.

Section CommaPaths.
Variables C D : category.
Variable q : functor C D.
Variable d : D.

Fixpoint induced_bar_lift_path_from (n : nat) :
    forall c (s : @path_from C n c) (a : hom D d (fobj q c)),
      @path_from (structured_category q d) n (structured_point q c a) :=
  match n as k return forall c (s : @path_from C k c) (a : hom D d (fobj q c)),
      @path_from (structured_category q d) k (structured_point q c a) with
  | O => fun _ _ _ => tt
  | S k => fun c s a =>
      match s with
      | existT e (f,t) =>
          existT _ (structured_point q e (compose a (fmap q f)))
            (@structured_morphism C D q d (structured_point q c a)
              (structured_point q e (compose a (fmap q f))) f (Logic.eq_refl _),
             @induced_bar_lift_path_from k e t (compose a (fmap q f)))
      end
  end.

Definition induced_bar_basis_to_comma n (s : induced_bar_basis q n d) :
    @path (structured_category q d) n :=
  match s with
  | existT (existT c t) a =>
      existT _ (structured_point q c a) (@induced_bar_lift_path_from n c t a)
  end.

Definition induced_bar_comma_to_basis n (s : @path (structured_category q d) n) :
    induced_bar_basis q n d :=
  match s with
  | existT X t => existT _
      (existT _ (structured_source X) (path_map_from (structured_projection q d) n X t))
      (structured_arrow X)
  end.

Lemma induced_bar_project_lift n c (s : @path_from C n c) a :
    path_map_from (structured_projection q d) n (structured_point q c a)
      (@induced_bar_lift_path_from n c s a) = s.
Proof.
revert c s a; induction n as [|n IH]; intros c s a.
- destruct s; reflexivity.
- destruct s as [e [f t]]; simpl; rewrite IH; reflexivity.
Qed.

Lemma induced_bar_lift_project n (X : structured_category q d)
    (s : @path_from (structured_category q d) n X) :
    @induced_bar_lift_path_from n (structured_source X)
      (path_map_from (structured_projection q d) n X s) (structured_arrow X) = s.
Proof.
revert X s; induction n as [|n IH]; intros X s.
- destruct s; reflexivity.
- destruct X as [c a]. destruct s as [[e b] [f t]].
  destruct f as [f hf]. change (hom C c e) in f. simpl in hf.
  destruct hf.
  simpl.
  have ih := IH (structured_point q e
    (@compose D d (fobj q c) (fobj q e) a (fmap q f))) t.
  simpl in ih.
  rewrite ih.
  reflexivity.
Qed.

Lemma induced_bar_comma_basis_inverse n (s : induced_bar_basis q n d) :
    induced_bar_comma_to_basis (induced_bar_basis_to_comma s) = s.
Proof.
destruct s as [[c t] a].
unfold induced_bar_comma_to_basis, induced_bar_basis_to_comma, path_map; simpl.
by rewrite induced_bar_project_lift.
Qed.

Lemma induced_bar_basis_comma_inverse n (s : @path (structured_category q d) n) :
    induced_bar_basis_to_comma (induced_bar_comma_to_basis s) = s.
Proof.
destruct s as [[c a] t].
unfold induced_bar_comma_to_basis, induced_bar_basis_to_comma, path_map; simpl.
have h := @induced_bar_lift_project n (structured_point q c a) t.
simpl in h; by rewrite h.
Qed.
End CommaPaths.

Arguments induced_bar_basis_to_comma {C D} q {d n} s.
Arguments induced_bar_comma_to_basis {C D} q {d n} s.
