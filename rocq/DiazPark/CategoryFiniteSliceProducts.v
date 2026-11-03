From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryLimits CategoryFinite
  CategoryFiniteProducts CategoryFinitePullbacks CategoryFiniteSlice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SliceTerminal.
Variable C : finite_category.
Variable T : fc_object C.

Definition fc_slice_terminal_point : fc_object (@fc_slice C T) :=
  existT _ T (fc_identity T).

Definition fc_slice_terminal_arrow (X : fc_object (@fc_slice C T)) :
    fc_hom (@fc_slice C T) X fc_slice_terminal_point.
Proof.
exists (projT2 X); apply/eqP; exact: fc_id_right.
Defined.

Definition fc_slice_terminal : terminal_object (fc_category (@fc_slice C T)).
Proof.
refine (@Build_terminal_object (fc_category (@fc_slice C T))
  fc_slice_terminal_point fc_slice_terminal_arrow _).
move=> X f; apply: val_inj.
have h := eqP (valP f).
change (fc_compose (val f) (fc_identity T) = projT2 X) in h.
by rewrite fc_id_right in h.
Defined.

End SliceTerminal.

Section SliceProducts.
Variable C : finite_category.
Variable T : fc_object C.
Variables P Q : @fc_slice_object C T.
Variable D : @finite_pullback_decomposition (fc_category C)
  (projT1 P) (projT1 Q) T (projT2 P) (projT2 Q).

Definition fc_pb_apex (i : pb_index D) : fc_object (@fc_slice C T) :=
  existT _ (pb_apex D i) (fc_compose (pb_left D i) (projT2 P)).

Definition fc_pb_left i : fc_hom (@fc_slice C T) (fc_pb_apex i) P.
Proof. exists (pb_left D i); exact: eqxx. Defined.

Definition fc_pb_right i : fc_hom (@fc_slice C T) (fc_pb_apex i) Q.
Proof. exists (pb_right D i); apply/eqP; symmetry; exact (pb_commutes D i). Defined.

Definition fc_pb_forget (X : fc_object (@fc_slice C T))
    (t : {i : pb_index D & fc_hom (@fc_slice C T) X (fc_pb_apex i)}) :
    {i : pb_index D & fc_hom C (projT1 X) (pb_apex D i)} :=
  existT _ (projT1 t) (val (projT2 t)).

Lemma fc_pb_forget_injective X : injective (@fc_pb_forget X).
Proof.
move=> [i f] [j g] h.
have he := existT_inj1 h; cbn in he; destruct he.
have hm := existT_inj2 h; f_equal; exact: val_inj hm.
Qed.

Lemma fc_pb_exists (X : fc_object (@fc_slice C T))
    (a : fc_hom (@fc_slice C T) X P) (b : fc_hom (@fc_slice C T) X Q) :
    exists t : {i : pb_index D & fc_hom (@fc_slice C T) X (fc_pb_apex i)},
      fc_compose (projT2 t) (fc_pb_left (projT1 t)) = a /\
      fc_compose (projT2 t) (fc_pb_right (projT1 t)) = b.
Proof.
have hc : fc_compose (val a) (projT2 P) = fc_compose (val b) (projT2 Q).
  by rewrite (eqP (valP a)) (eqP (valP b)).
have [[i h] [ha hb]] := pb_exists D (val a) (val b) hc.
cbn in ha, hb.
have hh : fc_compose h (fc_compose (pb_left D i) (projT2 P)) == projT2 X.
  apply/eqP; rewrite -fc_assoc ha; exact: eqP (valP a).
pose k : fc_hom (@fc_slice C T) X (fc_pb_apex i) := Sub h hh.
exists (existT _ i k); split; apply: val_inj; assumption.
Qed.

Definition fc_pb_lift X (a : fc_hom (@fc_slice C T) X P)
    (b : fc_hom (@fc_slice C T) X Q) :=
  proj1_sig (cid (fc_pb_exists a b)).

Lemma fc_pb_lift_left X a b :
    fc_compose (projT2 (@fc_pb_lift X a b))
      (fc_pb_left (projT1 (fc_pb_lift a b))) = a.
Proof. exact (proj1 (proj2_sig (cid (fc_pb_exists a b)))). Qed.

Lemma fc_pb_lift_right X a b :
    fc_compose (projT2 (@fc_pb_lift X a b))
      (fc_pb_right (projT1 (fc_pb_lift a b))) = b.
Proof. exact (proj2 (proj2_sig (cid (fc_pb_exists a b)))). Qed.

Lemma fc_pb_lift_unique X i (f : fc_hom (@fc_slice C T) X (fc_pb_apex i)) :
    fc_pb_lift (fc_compose f (fc_pb_left i)) (fc_compose f (fc_pb_right i)) =
      existT (fun j => fc_hom (@fc_slice C T) X (fc_pb_apex j)) i f.
Proof.
apply: fc_pb_forget_injective; apply: (pb_unique D).
- exact (congr1 val (fc_pb_lift_left (fc_compose f (fc_pb_left i))
    (fc_compose f (fc_pb_right i)))).
- exact (congr1 val (fc_pb_lift_right (fc_compose f (fc_pb_left i))
    (fc_compose f (fc_pb_right i)))).
Qed.

Definition fc_pullback_slice_product :
    @finite_product_decomposition (fc_category (@fc_slice C T)) P Q :=
  @Build_finite_product_decomposition (fc_category (@fc_slice C T)) P Q
    (pb_index D) fc_pb_apex fc_pb_left fc_pb_right
    (@fc_pb_lift) (@fc_pb_lift_left) (@fc_pb_lift_right) (@fc_pb_lift_unique).

End SliceProducts.

Print Assumptions fc_slice_terminal.
Print Assumptions fc_pullback_slice_product.
