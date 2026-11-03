(** An actual continuous open injection is homeomorphic to its literal image subtype. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology subtype_topology initial_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological.
Local Open Scope classical_set_scope.

Module DPTopologicalOpenImage.
Section Image.
Variables X Y : topologicalType.
Variable f : continuousType X Y.
Variable hinj : injective f.
Variable hopen : forall S : set X, open S -> open (f @` S).

Definition image_set : set Y := f @` [set: X].
Definition image_space := [the topologicalType of set_type image_set].
Definition image_forward (x : X) : image_space.
Proof. refine (exist _ (f x) _); apply/mem_set; by exists x. Defined.

Lemma image_preimage_exists (y : image_space) : exists x, f x = val y.
Proof. have [x _ e] := set_valP y; by exists x. Qed.
Definition image_inverse (y : image_space) : X :=
  proj1_sig (constructive_indefinite_description (image_preimage_exists y)).

Lemma image_inverse_equation y : f (image_inverse y) = val y.
Proof. exact: (proj2_sig (constructive_indefinite_description (image_preimage_exists y))). Qed.

Lemma image_forwardK : cancel image_forward image_inverse.
Proof. move=> x; apply: hinj; exact: image_inverse_equation. Qed.
Lemma image_inverseK : cancel image_inverse image_forward.
Proof. move=> y; apply: val_inj; exact: image_inverse_equation. Qed.

Lemma image_forward_continuous : continuous image_forward.
Proof. apply: (@continuous_comp_initial _ X Y set_val); exact: cts_fun. Qed.

Lemma image_inverse_continuous : continuous image_inverse.
Proof.
apply/continuousP => S hS.
exists (f @` S); first exact: hopen hS.
apply/seteqP; split=> y.
- move=> [x hx e].
  have ey : image_inverse y = x.
    apply: hinj; rewrite image_inverse_equation; exact: esym e.
  by rewrite /preimage /= ey.
- move=> hy; exists (image_inverse y); first exact hy.
  exact: image_inverse_equation.
Qed.

Definition open_image_homeomorphism : homeomorphism X image_space :=
  homeomorphism_of_inverse image_forward_continuous image_inverse_continuous
    image_forwardK image_inverseK.

Lemma open_image_homeomorphism_val x : val (iso_hom open_image_homeomorphism x) = f x.
Proof. reflexivity. Qed.

End Image.
End DPTopologicalOpenImage.
