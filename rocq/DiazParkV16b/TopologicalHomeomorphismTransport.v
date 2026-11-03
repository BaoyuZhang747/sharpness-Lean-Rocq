(** Literal transport of closed injections and T1 separation across actual homeomorphisms. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCoproductSubspaceImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalCoproductSubspaceImages.
Local Open Scope classical_set_scope.

Module DPTopologicalHomeomorphismTransport.
Lemma homeomorphism_closed_image {X Y : topologicalType} (e : homeomorphism X Y)
    (S : set X) (hS : closed S) : closed (iso_hom e @` S).
Proof.
rewrite homeomorphism_image_preimage; apply: preimage_closed => // y _; exact: cts_fun.
Qed.

Section Transport.
Variables A B C D : topologicalType.
Variables (eA : homeomorphism A C) (eB : homeomorphism B D).
Variables (f : continuousType A B) (g : continuousType C D).
Variable w : forall a, iso_hom eB (f a) = g (iso_hom eA a).

Lemma homeomorphic_map_injective (hg : injective g) : injective f.
Proof.
move=> a b e; apply: (@homeomorphism_injective _ _ eA); apply: hg.
by rewrite -!w e.
Qed.

Lemma homeomorphic_map_image (S : set A) :
  f @` S = iso_hom eB @^-1` (g @` (iso_hom eA @` S)).
Proof.
apply/seteqP; split=> b.
- move=> [a ha <-]; exists (iso_hom eA a); first by exists a.
  symmetry; exact: w.
- move=> [c [a ha ea] eb]; exists a => //.
  apply: (@homeomorphism_injective _ _ eB); rewrite w ea; exact eb.
Qed.

Theorem homeomorphic_map_closed (hg : forall S : set C, closed S -> closed (g @` S))
    (S : set A) (hS : closed S) : closed (f @` S).
Proof.
rewrite homeomorphic_map_image; apply: preimage_closed.
- move=> b _; exact: cts_fun.
- apply: hg; exact: homeomorphism_closed_image hS.
Qed.
End Transport.

Theorem homeomorphism_accessible {X Y : topologicalType} (e : homeomorphism X Y)
    (hY : accessible_space Y) : accessible_space X.
Proof.
have hclosed (x : X) : closed [set x].
  have eS : [set x] = iso_hom e @^-1` [set iso_hom e x].
    apply/seteqP; split=> y hy.
    * by rewrite hy.
    * exact: (@homeomorphism_injective _ _ e y x hy).
  rewrite eS; apply: preimage_closed.
  - move=> y _; exact: cts_fun.
  - exact (@accessible_closed_set1 Y hY (iso_hom e x)).
move=> x y hxy; exists (~` [set y]); rewrite !inE /=; split.
- rewrite openC; exact: hclosed.
- exact/eqP.
- by [].
Qed.
End DPTopologicalHomeomorphismTransport.
