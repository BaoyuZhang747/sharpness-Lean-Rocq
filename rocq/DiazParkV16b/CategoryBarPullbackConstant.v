From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex BarPaths BarComplex.
From DiazParkV16b Require Import CategoryBarPullbackPaths CategoryBarPullback.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkBarPaths DiazParkBarComplex
  DPCategoryBarPullback DPCategoryBarPullbackMaps.
Local Open Scope ring_scope.

Module DPCategoryBarConstant.

Definition constant_coefficient (R : pzRingType) (C : category) (A : lmodType R) :
    module_codiagram R C.
Proof.
refine (@Build_functor (opposite C) (module_category R)
  (fun _ => A) (fun _ _ _ => module_hom_id A) _ _).
- intro x; reflexivity.
- intros x y z f g; apply module_hom_ext; intro a; reflexivity.
Defined.

Arguments constant_coefficient R C A : clear implicits.

Definition constant_bar (R : pzRingType) (C : category) (A : lmodType R) :
    @cochain_complex R := bar_complex (constant_coefficient R C A).

Arguments constant_bar R C A : clear implicits.

Section Pullback.
Variable R : pzRingType.
Variable A : lmodType R.
Variables C D : category.
Variable F : functor C D.

Definition constant_bar_pullback :
    cochain_map (constant_bar R D A) (constant_bar R C A) :=
  @CochainMap R (constant_bar R D A) (constant_bar R C A)
    (fun n => (bar_pullback_at F (constant_coefficient R D A) n :
      {linear cochain_term (constant_bar R D A) n -> cochain_term (constant_bar R C A) n}))
    (@bar_pullback_d R C D F (constant_coefficient R D A)).

Lemma constant_bar_pullback_at n (a : cochain_term (constant_bar R D A) n)
    x (p : @path_from C n x) :
  cochain_map_at constant_bar_pullback n a x p =
    a (fobj F x) (path_map_from F n x p).
Proof. reflexivity. Qed.

End Pullback.

Arguments constant_bar_pullback {R} A {C D} F.

Lemma constant_bar_pullback_identity (R : pzRingType) (C : category)
    (A : lmodType R) n (a : cochain_term (constant_bar R C A) n) :
  cochain_map_at (constant_bar_pullback A (functor_id C)) n a = a.
Proof. exact (@bar_pullback_identity R C (constant_coefficient R C A) n a). Qed.

Lemma constant_bar_pullback_composition (R : pzRingType) (C D E : category)
    (A : lmodType R) (F : functor C D) (G : functor D E)
    n (a : cochain_term (constant_bar R E A) n) :
  cochain_map_at (constant_bar_pullback A (functor_comp F G)) n a =
    cochain_map_at (constant_bar_pullback A F) n
      (cochain_map_at (constant_bar_pullback A G) n a).
Proof. exact (@bar_pullback_composition R C D E F G (constant_coefficient R E A) n a). Qed.

End DPCategoryBarConstant.
