From mathcomp Require Import all_boot.
From DiazPark Require Import Category CategoryComma CategoryFinite CategoryFinitePullbacks.

(** The finite presentation of an actual slice category: objects are actual
    arrows and morphisms are actual commuting triangles. The functor into
    the general slice category preserves these data literally. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FiniteSlice.
Variable C : finite_category.
Variable T : fc_object C.

Definition fc_slice_object := {x : fc_object C & fc_hom C x T}.
Definition fc_slice_hom (x y : fc_slice_object) :=
  {h : fc_hom C (projT1 x) (projT1 y) |
    fc_compose h (projT2 y) == projT2 x}.

Definition fc_slice_identity (x : fc_slice_object) : fc_slice_hom x x.
Proof. exists (fc_identity (projT1 x)); by rewrite fc_id_left eqxx. Defined.

Definition fc_slice_compose (x y z : fc_slice_object)
    (f : fc_slice_hom x y) (g : fc_slice_hom y z) : fc_slice_hom x z.
Proof.
exists (fc_compose (val f) (val g)).
by rewrite fc_assoc (eqP (valP g)) (eqP (valP f)).
Defined.

Definition fc_slice : finite_category.
Proof.
refine {| fc_object := [the finType of fc_slice_object];
          fc_hom := fun x y => [the finType of fc_slice_hom x y];
          fc_identity := fc_slice_identity;
          fc_compose := fun x y z f g => @fc_slice_compose x y z f g |}.
- move=> x y f; apply: val_inj; exact: fc_id_left.
- move=> x y f; apply: val_inj; exact: fc_id_right.
- move=> w x y z f g h; apply: val_inj; exact: fc_assoc.
Defined.

Definition fc_slice_to_over_object (x : fc_slice_object) :
    over_category (fc_category C) T :=
  @over_object (fc_category C) (projT1 x) T (projT2 x).

Definition fc_slice_to_over_map (x y : fc_slice_object) (f : fc_slice_hom x y) :
    hom (over_category (fc_category C) T)
      (fc_slice_to_over_object x) (fc_slice_to_over_object y).
Proof.
refine (@Build_costructured_hom (fc_category C) (fc_category C)
  (functor_id (fc_category C)) T (fc_slice_to_over_object x)
  (fc_slice_to_over_object y) (val f) _).
exact: eqP (valP f).
Defined.

Definition fc_slice_to_over :
    functor (fc_category fc_slice) (over_category (fc_category C) T).
Proof.
refine (@Build_functor (fc_category fc_slice) (over_category (fc_category C) T)
  fc_slice_to_over_object (@fc_slice_to_over_map) _ _).
- move=> x; apply costructured_hom_ext; reflexivity.
- move=> x y z f g; apply costructured_hom_ext; reflexivity.
Defined.

Definition fc_over_to_slice_object (x : over_category (fc_category C) T) :
    fc_slice_object := existT _ (costructured_source x) (costructured_arrow x).

Definition fc_over_to_slice_map (x y : over_category (fc_category C) T)
    (f : hom (over_category (fc_category C) T) x y) :
    fc_slice_hom (fc_over_to_slice_object x) (fc_over_to_slice_object y).
Proof.
exists (costructured_map f); apply/eqP; exact (costructured_commutes f).
Defined.

Definition fc_over_to_slice :
    functor (over_category (fc_category C) T) (fc_category fc_slice).
Proof.
refine (@Build_functor (over_category (fc_category C) T) (fc_category fc_slice)
  fc_over_to_slice_object (@fc_over_to_slice_map) _ _).
- move=> x; apply: val_inj; reflexivity.
- move=> x y z f g; apply: val_inj; reflexivity.
Defined.

Lemma fc_slice_object_roundtrip x :
    fc_over_to_slice_object (fc_slice_to_over_object x) = x.
Proof. by case: x. Qed.

Lemma fc_over_object_roundtrip x :
    fc_slice_to_over_object (fc_over_to_slice_object x) = x.
Proof. by case: x. Qed.

Lemma fc_slice_map_injective x y : injective (@fc_slice_to_over_map x y).
Proof.
move=> f g h; apply: val_inj.
exact (f_equal (@costructured_map (fc_category C) (fc_category C)
  (functor_id (fc_category C)) T (fc_slice_to_over_object x)
  (fc_slice_to_over_object y)) h).
Qed.

Lemma fc_slice_map_surjective x y
    (f : hom (over_category (fc_category C) T)
      (fc_slice_to_over_object x) (fc_slice_to_over_object y)) :
    exists g : fc_slice_hom x y, fc_slice_to_over_map g = f.
Proof.
have hf : fc_compose (costructured_map f) (projT2 y) == projT2 x.
  apply/eqP; exact (costructured_commutes f).
exists (Sub (costructured_map f) hf).
apply costructured_hom_ext; reflexivity.
Qed.

End FiniteSlice.

Print Assumptions fc_slice.
Print Assumptions fc_slice_to_over.
Print Assumptions fc_slice_map_surjective.
