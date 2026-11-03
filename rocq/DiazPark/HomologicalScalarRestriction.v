(** Restriction of arbitrary module scalars along an arbitrary unital ring
    homomorphism. No finiteness, flatness, or nonzero-ring hypothesis. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DiazParkScalarRestriction.
Section Restriction.
Variables A B : pzRingType.
Variable f : {rmorphism A -> B}.

Section Module.
Variable V : lmodType B.

Definition restricted_module := let _ := f in (V : Type).
HB.instance Definition _ := GRing.Zmodule.on restricted_module.
Definition restricted_scale (a : A) (v : restricted_module) : restricted_module := f a *: (v : V).
Lemma restricted_scaleA a b v :
  restricted_scale a (restricted_scale b v) = restricted_scale (a * b) v.
Proof. by rewrite /restricted_scale rmorphM scalerA. Qed.
Lemma restricted_scale1 : left_id 1 restricted_scale.
Proof. by move=> v; rewrite /restricted_scale rmorph1 scale1r. Qed.
Lemma restricted_scaleD : right_distributive restricted_scale +%R.
Proof. move=> a x y; exact: scalerDr. Qed.
Lemma restricted_scaleDl v a b :
  restricted_scale (a + b) v = restricted_scale a v + restricted_scale b v.
Proof. by rewrite /restricted_scale rmorphD scalerDl. Qed.
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build A restricted_module
  restricted_scaleA restricted_scale1 restricted_scaleD restricted_scaleDl.
Definition restricted_module_type : lmodType A := [the lmodType A of restricted_module].
End Module.

Section Map.
Variables U V : lmodType B.
Variable g : {linear U -> V}.
Definition restricted_linear_fun (x : restricted_module_type U) : restricted_module_type V :=
  g x.
Lemma restricted_linearP : linear restricted_linear_fun.
Proof. move=> a x y; exact: linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build A (restricted_module_type U)
  (restricted_module_type V) _ restricted_linear_fun restricted_linearP.
Definition restricted_linear : {linear restricted_module_type U -> restricted_module_type V} :=
  restricted_linear_fun.
End Map.

Definition restricted_hom {U V : lmodType B} (g : module_hom U V) :
    module_hom (restricted_module_type U) (restricted_module_type V) :=
  module_hom_of_linear (restricted_linear (module_hom_to_linear g)).

Definition restriction_functor : functor (module_category B) (module_category A).
Proof.
refine (@Build_functor (module_category B) (module_category A)
  restricted_module_type (fun U V g => restricted_hom g) _ _).
- move=> U; apply module_hom_ext => v; reflexivity.
- move=> U V W g h; apply module_hom_ext => v; reflexivity.
Defined.

Definition restriction_diagram {C : category} (D : module_diagram B C) :
    module_diagram A C := functor_comp D restriction_functor.

Definition restriction_map {C : category} {D E : module_diagram B C}
    (u : nat_trans D E) : nat_trans (restriction_diagram D) (restriction_diagram E) :=
  nat_whisker_right u restriction_functor.

End Restriction.
End DiazParkScalarRestriction.
