(** A genuine closed continuous injection is homeomorphic to its literal image. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology
  subtype_topology initial_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalOpenImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalClosedImage.
Import DPTopological DPTopologicalOpenImage.
Section Image.
Variables X Y : topologicalType.
Variable f : continuousType X Y.
Variable hi : injective f.
Variable hc : forall S : set X, closed S -> closed (f @` S).

Lemma closed_image_inverse_continuous : continuous ((@image_inverse X Y f)).
Proof.
apply/continuous_closedP => S hS.
have e : (@image_inverse X Y f) @^-1` S = (@set_val Y (image_set f)) @^-1` (f @` S).
  apply/predeqP => y; split.
  - move=> hy; exists ((@image_inverse X Y f) y); first exact hy.
    exact: image_inverse_equation.
  - move=> [x hx e].
    have ey : (@image_inverse X Y f) y = x.
      apply hi; rewrite image_inverse_equation; exact: esym e.
    change (S ((@image_inverse X Y f) y)); by rewrite ey.
rewrite e; apply: preimage_closed; last exact: hc hS.
by move=> y hy; exact: initial_continuous.
Qed.

Definition closed_image_homeomorphism : homeomorphism X (image_space f) :=
  homeomorphism_of_inverse (@image_forward_continuous X Y f) closed_image_inverse_continuous
    (@image_forwardK X Y f hi) (@image_inverseK X Y f).

Lemma closed_image_homeomorphism_val x :
  val (iso_hom closed_image_homeomorphism x) = f x.
Proof. reflexivity. Qed.

Definition closed_image_lift_function {Z : topologicalType} (g : continuousType Z Y)
  (hg : forall z, range f (g z)) (z : Z) : X :=
  @image_inverse X Y f (exist _ (g z) (mem_set (hg z))).

Lemma closed_image_lift_continuous {Z : topologicalType} (g : continuousType Z Y)
  (hg : forall z, range f (g z)) : continuous (closed_image_lift_function hg).
Proof.
pose lifted (z : Z) : image_space f := exist _ (g z) (mem_set (hg z)).
have hl : continuous lifted.
  apply: (@continuous_comp_initial _ Z Y set_val); exact: cts_fun.
move=> z; exact (@continuous_comp Z (image_space f) X lifted
  (@image_inverse X Y f) z (hl z) (@closed_image_inverse_continuous (lifted z))).
Qed.

Definition closed_image_lift {Z : topologicalType} (g : continuousType Z Y)
  (hg : forall z, range f (g z)) : continuousType Z X :=
  @continuous_map Z X (closed_image_lift_function hg) (@closed_image_lift_continuous Z g hg).

Lemma closed_image_lift_equation {Z : topologicalType} (g : continuousType Z Y)
  (hg : forall z, range f (g z)) z : f (closed_image_lift hg z) = g z.
Proof.
change (f (@image_inverse X Y f (exist _ (g z) (mem_set (hg z)))) = g z).
exact (@image_inverse_equation X Y f (exist _ (g z) (mem_set (hg z)))).
Qed.
End Image.
End DPTopologicalClosedImage.
