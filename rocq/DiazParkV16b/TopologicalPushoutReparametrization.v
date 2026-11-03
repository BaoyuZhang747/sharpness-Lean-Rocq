(** Actual pushouts are preserved by changing source and cell coordinates through homeomorphisms. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPCategoryPushout.
Module DPTopologicalPushoutReparametrization.
Section Reparametrization.
Variables A B X Y A0 B0 : topologicalType.
Variables (i : continuousType A B) (p : continuousType A X)
  (q : continuousType B Y) (j : continuousType X Y).
Variable h : @pushout_square topological_category A B X Y i p q j.
Variables (eA : homeomorphism A0 A) (eB : homeomorphism B0 B) (i0 : continuousType A0 B0).
Variable hi0 : forall a, iso_hom eB (i0 a) = i (iso_hom eA a).
Let p0 := continuous_compose (iso_hom eA) p.
Let q0 := continuous_compose (iso_hom eB) q.

Lemma reparametrized_commutes : @compose topological_category _ _ _ i0 q0 = @compose topological_category _ _ _ p0 j.
Proof.
apply: topological_hom_ext => a.
change (q (iso_hom eB (i0 a)) = j (p (iso_hom eA a))).
rewrite hi0.
exact (congr1 (fun f : continuousType A Y => f (iso_hom eA a)) (pushout_commutes h)).
Qed.

Section Descent.
Variable Z : topologicalType.
Variables (f : continuousType B0 Z) (g : continuousType X Z).
Variable w : @compose topological_category _ _ _ i0 f = @compose topological_category _ _ _ p0 g.
Let f' := continuous_compose (iso_inv eB) f.

Lemma reparametrized_original_compatibility : @compose topological_category _ _ _ i f' = @compose topological_category _ _ _ p g.
Proof.
apply: topological_hom_ext => a.
have h0 : iso_inv eB (i a) = i0 (iso_inv eA a).
  apply: (@homeomorphism_injective B0 B eB).
  by rewrite homeomorphism_inverseK hi0 homeomorphism_inverseK.
change (f (iso_inv eB (i a)) = g (p a)).
rewrite h0.
have ew := congr1 (fun k : continuousType A0 Z => k (iso_inv eA a)) w.
change (f (i0 (iso_inv eA a)) = g (p (iso_hom eA (iso_inv eA a)))) in ew.
by rewrite homeomorphism_inverseK in ew.
Qed.

Definition reparametrized_desc : continuousType Y Z :=
  pushout_desc h f' g reparametrized_original_compatibility.

Lemma reparametrized_desc_left : @compose topological_category _ _ _ q0 reparametrized_desc = f.
Proof.
apply: topological_hom_ext => b.
have e := congr1 (fun k : continuousType B Z => k (iso_hom eB b))
  (pushout_desc_left h f' g reparametrized_original_compatibility).
change (reparametrized_desc (q (iso_hom eB b)) = f (iso_inv eB (iso_hom eB b))) in e.
by rewrite homeomorphism_forwardK in e.
Qed.
Lemma reparametrized_desc_right : @compose topological_category _ _ _ j reparametrized_desc = g.
Proof. exact: pushout_desc_right. Qed.
Lemma reparametrized_desc_unique (t : continuousType Y Z)
    (hl : @compose topological_category _ _ _ q0 t = f)
    (hr : @compose topological_category _ _ _ j t = g) : t = reparametrized_desc.
Proof.
apply: (pushout_desc_unique h f' g reparametrized_original_compatibility t); last exact hr.
apply: topological_hom_ext => b.
have e := congr1 (fun k : continuousType B0 Z => k (iso_inv eB b)) hl.
change (t (q (iso_hom eB (iso_inv eB b))) = f (iso_inv eB b)) in e.
by rewrite homeomorphism_inverseK in e.
Qed.
End Descent.

Definition reparametrized_pushout : @pushout_square topological_category A0 B0 X Y i0 p0 q0 j.
Proof.
refine (@Build_pushout_square topological_category A0 B0 X Y i0 p0 q0 j
  reparametrized_commutes (fun Z f g w => @reparametrized_desc Z f g w) _ _ _).
- move=> Z f g w; exact: reparametrized_desc_left.
- move=> Z f g w; exact: reparametrized_desc_right.
- move=> Z f g w t; exact: reparametrized_desc_unique.
Defined.
End Reparametrization.
End DPTopologicalPushoutReparametrization.
