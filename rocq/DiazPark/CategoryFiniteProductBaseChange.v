From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryFiniteProducts CategoryFinitePullbacks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BaseChange.
Variable C : category.
Variables P Q Q' : C.
Variable D : @finite_product_decomposition C P Q.
Variable f : hom C Q' Q.
Variable B : forall i : fp_index D, finite_pullback_decomposition (fp_right D i) f.

Definition fp_basechange_index := {i : fp_index D & pb_index (B i)}.
Definition fp_basechange_apex (z : fp_basechange_index) := pb_apex (B (projT1 z)) (projT2 z).
Definition fp_basechange_left (z : fp_basechange_index) :=
  compose (pb_left (B (projT1 z)) (projT2 z)) (fp_left D (projT1 z)).
Definition fp_basechange_right (z : fp_basechange_index) := pb_right (B (projT1 z)) (projT2 z).

Lemma fp_basechange_exists (X : C) (a : hom C X P) (b : hom C X Q') :
    exists z : {i : fp_basechange_index & hom C X (fp_basechange_apex i)},
      compose (projT2 z) (fp_basechange_left (projT1 z)) = a /\
      compose (projT2 z) (fp_basechange_right (projT1 z)) = b.
Proof.
case he : (fp_lift D a (compose b f))=> [i h].
have h1 := fp_lift_left D a (compose b f).
have h2 := fp_lift_right D a (compose b f).
rewrite he /= in h1 h2.
have [[j u] [hu hb]] := pb_exists (B i) h b h2.
exists (existT _ (existT _ i j) u); split=> /=.
- by rewrite /fp_basechange_left /= -compose_assoc hu h1.
- exact hb.
Qed.

Lemma fp_basechange_unique (X : C)
    (z w : {i : fp_basechange_index & hom C X (fp_basechange_apex i)}) :
    compose (projT2 z) (fp_basechange_left (projT1 z)) =
      compose (projT2 w) (fp_basechange_left (projT1 w)) ->
    compose (projT2 z) (fp_basechange_right (projT1 z)) =
      compose (projT2 w) (fp_basechange_right (projT1 w)) -> z = w.
Proof.
case: z=> [[i j] u]; case: w=> [[k l] v] /=.
rewrite /fp_basechange_left /fp_basechange_right /= => h1 h2.
have hD : existT (fun n => hom C X (fp_apex D n)) i (compose u (pb_left (B i) j)) =
    existT (fun n => hom C X (fp_apex D n)) k (compose v (pb_left (B k) l)).
  apply: fp_encode_injective.
  rewrite /fp_encode /= !compose_assoc h1.
  congr (_, _).
  by rewrite !pb_commutes -!compose_assoc h2.
have hik := existT_inj1 hD; subst k.
have hL := existT_inj2 hD.
have hB : existT (fun n => hom C X (pb_apex (B i) n)) j u =
    existT (fun n => hom C X (pb_apex (B i) n)) l v.
  apply: (@pb_unique C _ _ _ _ _ (B i) X); [exact hL | exact h2].
have hjl := existT_inj1 hB; subst l.
have huv := existT_inj2 hB; subst v; reflexivity.
Qed.

Definition fp_basechange_lift (X : C) (a : hom C X P) (b : hom C X Q') :=
  proj1_sig (cid (fp_basechange_exists a b)).

Definition fp_basechange : @finite_product_decomposition C P Q'.
Proof.
refine (@Build_finite_product_decomposition C P Q'
  [the finType of fp_basechange_index] fp_basechange_apex
  fp_basechange_left fp_basechange_right fp_basechange_lift _ _ _).
- move=> X a b; exact: (proj2_sig (cid (fp_basechange_exists a b))).1.
- move=> X a b; exact: (proj2_sig (cid (fp_basechange_exists a b))).2.
- move=> X i h; apply: fp_basechange_unique.
  + exact: (proj2_sig (cid (fp_basechange_exists
      (compose h (fp_basechange_left i)) (compose h (fp_basechange_right i))))).1.
  + exact: (proj2_sig (cid (fp_basechange_exists
      (compose h (fp_basechange_left i)) (compose h (fp_basechange_right i))))).2.
Defined.
End BaseChange.

Arguments fp_basechange {C P Q Q'} D f B.
Arguments fp_basechange_apex {C P Q Q'} D f B z.
Arguments fp_basechange_left {C P Q Q'} D f B z.
Arguments fp_basechange_right {C P Q Q'} D f B z.

Print Assumptions fp_basechange.
