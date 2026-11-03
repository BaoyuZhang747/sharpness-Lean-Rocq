(** The dual of the proved universal-arrow adjunction constructor. Applications
    supply a genuinely proved unique lifting property, not an adjunction premise. *)
From DiazPark Require Import Category CategoryAdjunction.
From DiazParkV16b Require Import CategoryUniversalReflection.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryUniversalCoreflection.
Section Universal.
Variables C D : category.
Variable J : functor D C.
Variable obj : C -> D.
Variable counit : forall x : C, hom C (fobj J (obj x)) x.
Hypothesis universal : forall (x : C) (y : D) (f : hom C (fobj J y) x),
  exists! g : hom D y (obj x), compose (fmap J g) (counit x) = f.

Let dual := @DPCategoryUniversalReflection.reflection (opposite C) (opposite D)
  (functor_op J) obj counit universal.
Let dual_adjunction := @DPCategoryUniversalReflection.reflection_adjunction
  (opposite C) (opposite D) (functor_op J) obj counit universal.

Definition coreflection : functor C D.
Proof.
refine (@Build_functor C D obj (fun x y f => @fmap (opposite C) (opposite D) dual y x f) _ _).
- intro x; exact (fmap_id dual x).
- intros x y z f g; exact (fmap_compose dual g f).
Defined.

Definition coreflection_adjunction : adjunction J coreflection.
Proof.
refine (@Build_adjunction D C J coreflection
  (@Build_nat_trans D D (functor_id D) (functor_comp J coreflection)
    (fun x => component (adj_counit dual_adjunction) x)
    (fun x y f => eq_sym (naturality (adj_counit dual_adjunction) f)))
  (@Build_nat_trans C C (functor_comp coreflection J) (functor_id C) counit
    (fun x y f => eq_sym (naturality (adj_unit dual_adjunction) f))) _ _).
- intro x; exact (adj_triangle_right dual_adjunction x).
- intro x; exact (adj_triangle_left dual_adjunction x).
Defined.

Lemma coreflection_counit (x : C) :
  component (adj_counit coreflection_adjunction) x = counit x.
Proof. reflexivity. Qed.

Lemma coreflection_map_spec (x y : C) (f : hom C x y) :
  compose (fmap J (fmap coreflection f)) (counit y) = compose (counit x) f.
Proof.
exact (@DPCategoryUniversalReflection.reflection_map_spec (opposite C) (opposite D)
  (functor_op J) obj counit universal y x f).
Qed.
End Universal.
End DPCategoryUniversalCoreflection.
