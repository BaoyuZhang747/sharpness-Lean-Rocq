(** The native MathComp linear-map adapter for ordinary categorical maps.
    Both adapters preserve the underlying function definitionally. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From DiazPark Require Import CategoryModules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NativeLinear.
Variable R : pzRingType.
Variables U V : lmodType R.
Variable f : module_hom U V.

HB.instance Definition _ := GRing.isLinear.Build R U V _
  (module_hom_fun f) (module_hom_linear f).

Definition module_hom_to_linear : {linear U -> V} := module_hom_fun f.

Lemma module_hom_to_linear_apply x : module_hom_to_linear x = f x.
Proof. reflexivity. Qed.

Lemma module_hom_linear_roundtrip :
  module_hom_of_linear module_hom_to_linear = f.
Proof. apply module_hom_ext. intro x. reflexivity. Qed.
End NativeLinear.

Arguments module_hom_to_linear {R U V} f.

Print Assumptions module_hom_to_linear.
Print Assumptions module_hom_linear_roundtrip.
