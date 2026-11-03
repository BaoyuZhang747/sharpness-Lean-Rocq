From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialSubcomplex.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet.

(** Genuine degreewise subsets, closed under every ordinal action. *)
Record subcomplex (X : simplicial_set) := Subcomplex {
  member : forall n, simplex X n -> Prop;
  member_closed : forall n m (f : ordinal_map n m) (x : simplex X m),
    @member m x -> @member n (simplex_map X f x)
}.

Arguments member {_} _ _ _.
Arguments member_closed {_} _ {_ _} _ _ _.

Definition subcomplex_le {X : simplicial_set} (S T : subcomplex X) : Prop :=
  forall n x, member S n x -> member T n x.

Lemma subcomplex_le_refl X (S : subcomplex X) : subcomplex_le S S.
Proof. intros n x h. exact h. Qed.

Lemma subcomplex_le_trans X (S T U : subcomplex X) :
  subcomplex_le S T -> subcomplex_le T U -> subcomplex_le S U.
Proof. intros hST hTU n x hx. exact (hTU n x (hST n x hx)). Qed.

Lemma subcomplex_ext X (S T : subcomplex X) :
  (forall n x, member S n x <-> member T n x) -> S = T.
Proof.
  destruct S as [S hS], T as [T hT]; cbn. intro h.
  have e : S = T.
  { apply functional_extensionality_dep. intro n.
    apply functional_extensionality_dep. intro x.
    apply propositional_extensionality. exact (h n x). }
  destruct e. f_equal. apply Prop_irrelevance.
Qed.

Lemma subcomplex_le_antisymm X (S T : subcomplex X) :
  subcomplex_le S T -> subcomplex_le T S -> S = T.
Proof. intros hST hTS. apply subcomplex_ext. intros n x. split; auto. Qed.

Definition subcomplex_simplex X (S : subcomplex X) n :=
  {x : simplex X n | member S n x}.

Lemma subcomplex_simplex_ext X (S : subcomplex X) n
    (x y : subcomplex_simplex S n) : proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x hx], y as [y hy]; cbn. intro e. subst y.
  f_equal. apply Prop_irrelevance.
Qed.

Definition subcomplex_set X (S : subcomplex X) : simplicial_set.
Proof.
  refine (@Build_functor (opposite simplex_category) type_category
    (fun n => subcomplex_simplex S n)
    (fun n m f x => exist _ (simplex_map X f (proj1_sig x))
      (member_closed S f (proj1_sig x) (proj2_sig x))) _ _).
  - intro n. apply type_morphism_ext. intro x.
    apply subcomplex_simplex_ext. apply simplex_map_identity.
  - intros n m k f g. apply type_morphism_ext. intro x.
    apply subcomplex_simplex_ext. apply simplex_map_compose.
Defined.

Arguments subcomplex_set {_} _.

Definition subcomplex_inclusion X (S : subcomplex X) :
  simplicial_map (subcomplex_set S) X.
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (subcomplex_set S) X (fun n x => proj1_sig x) _).
  intros n m f. reflexivity.
Defined.

Arguments subcomplex_inclusion {_} _.

Lemma subcomplex_inclusion_injective X (S : subcomplex X) n :
  injective (component (subcomplex_inclusion S) n).
Proof. intros x y h. apply subcomplex_simplex_ext. exact h. Qed.

Definition subcomplex_map X (S T : subcomplex X) (h : subcomplex_le S T) :
  simplicial_map (subcomplex_set S) (subcomplex_set T).
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (subcomplex_set S) (subcomplex_set T)
    (fun n x => exist _ (proj1_sig x) (h n (proj1_sig x) (proj2_sig x))) _).
  intros n m f. apply type_morphism_ext. intro x.
  apply subcomplex_simplex_ext. reflexivity.
Defined.

Arguments subcomplex_map {_ _ _} _.

Lemma subcomplex_map_inclusion X (S T : subcomplex X) (h : subcomplex_le S T) :
  nat_comp (subcomplex_map h) (subcomplex_inclusion T) = subcomplex_inclusion S.
Proof. apply nat_trans_ext. intro n. reflexivity. Qed.

Lemma subcomplex_map_identity X (S : subcomplex X) (h : subcomplex_le S S) :
  subcomplex_map h = nat_id (subcomplex_set S).
Proof.
  apply nat_trans_ext. intro n. apply type_morphism_ext. intro x.
  apply subcomplex_simplex_ext. reflexivity.
Qed.

Lemma subcomplex_map_compose X (S T U : subcomplex X)
    (h : subcomplex_le S T) (k : subcomplex_le T U) (l : subcomplex_le S U) :
  nat_comp (subcomplex_map h) (subcomplex_map k) = subcomplex_map l.
Proof.
  apply nat_trans_ext. intro n. apply type_morphism_ext. intro x.
  apply subcomplex_simplex_ext. reflexivity.
Qed.

Definition subcomplex_top (X : simplicial_set) : subcomplex X.
Proof. refine (@Subcomplex X (fun _ _ => True) _). intros; exact I. Defined.

Definition subcomplex_bottom (X : simplicial_set) : subcomplex X.
Proof. refine (@Subcomplex X (fun _ _ => False) _). intros n m f x h; contradiction. Defined.

Definition subcomplex_intersection X (S T : subcomplex X) : subcomplex X.
Proof.
  refine (@Subcomplex X (fun n x => member S n x /\ member T n x) _).
  intros n m f x [hS hT]. split.
  - exact (member_closed S f x hS).
  - exact (member_closed T f x hT).
Defined.

Definition subcomplex_union X (S T : subcomplex X) : subcomplex X.
Proof.
  refine (@Subcomplex X (fun n x => member S n x \/ member T n x) _).
  intros n m f x [hS|hT].
  - left. exact (member_closed S f x hS).
  - right. exact (member_closed T f x hT).
Defined.

Definition subcomplex_iUnion X (I : Type) (S : I -> subcomplex X) : subcomplex X.
Proof.
  refine (@Subcomplex X (fun n x => exists i, member (S i) n x) _).
  intros n m f x [i hi]. exists i. exact (member_closed (S i) f x hi).
Defined.

End DPSimplicialSubcomplex.
