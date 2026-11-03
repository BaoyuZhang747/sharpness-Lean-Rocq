From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryFiniteProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Comparison.
Variable C : category.
Variables P Q : C.
Variables D E : @finite_product_decomposition C P Q.

Definition fp_compare_index (i : fp_index D) :=
  projT1 (fp_lift E (fp_left D i) (fp_right D i)).
Definition fp_compare_arrow (i : fp_index D) :
    hom C (fp_apex D i) (fp_apex E (fp_compare_index i)) :=
  projT2 (fp_lift E (fp_left D i) (fp_right D i)).

Lemma fp_compare_left i :
    compose (fp_compare_arrow i) (fp_left E (fp_compare_index i)) = fp_left D i.
Proof. exact: fp_lift_left. Qed.

Lemma fp_compare_right i :
    compose (fp_compare_arrow i) (fp_right E (fp_compare_index i)) = fp_right D i.
Proof. exact: fp_lift_right. Qed.

Lemma fp_compare_iso_exists i :
    exists e : @isomorphism C (fp_apex D i) (fp_apex E (fp_compare_index i)),
      iso_hom e = fp_compare_arrow i.
Proof.
rewrite /fp_compare_index /fp_compare_arrow.
case he : (fp_lift E (fp_left D i) (fp_right D i))=> [j f] /=.
have hf1 := fp_lift_left E (fp_left D i) (fp_right D i).
have hf2 := fp_lift_right E (fp_left D i) (fp_right D i).
rewrite he /= in hf1 hf2.
case hd : (fp_lift D (fp_left E j) (fp_right E j))=> [k g] /=.
have hg1 := fp_lift_left D (fp_left E j) (fp_right E j).
have hg2 := fp_lift_right D (fp_left E j) (fp_right E j).
rewrite hd /= in hg1 hg2.
have hfg : existT (fun n => hom C (fp_apex D i) (fp_apex D n)) k (compose f g) =
    existT (fun n => hom C (fp_apex D i) (fp_apex D n)) i (identity (fp_apex D i)).
  apply: fp_encode_injective.
  by rewrite /fp_encode /= !compose_assoc hg1 hg2 hf1 hf2 !compose_id_left.
have hki := existT_inj1 hfg; subst k.
have hfg0 := existT_inj2 hfg.
have hgf : compose g f = identity (fp_apex E j).
  have hh : existT (fun n => hom C (fp_apex E j) (fp_apex E n)) j (compose g f) =
      existT (fun n => hom C (fp_apex E j) (fp_apex E n)) j (identity (fp_apex E j)).
    apply: fp_encode_injective.
    by rewrite /fp_encode /= !compose_assoc hf1 hf2 hg1 hg2 !compose_id_left.
  exact: existT_inj2 hh.
exists (@Build_isomorphism C _ _ f g hfg0 hgf); reflexivity.
Qed.

Definition fp_compare_iso i := proj1_sig (cid (fp_compare_iso_exists i)).

Lemma fp_compare_iso_hom i : iso_hom (fp_compare_iso i) = fp_compare_arrow i.
Proof. exact: proj2_sig (cid (fp_compare_iso_exists i)). Qed.

Lemma fp_compare_index_unique i j (e : @isomorphism C (fp_apex D i) (fp_apex E j)) :
    compose (iso_hom e) (fp_left E j) = fp_left D i ->
    compose (iso_hom e) (fp_right E j) = fp_right D i ->
    fp_compare_index i = j.
Proof.
move=> h1 h2; rewrite /fp_compare_index -h1 -h2 fp_unique; reflexivity.
Qed.

End Comparison.

Arguments fp_compare_index {C P Q} D E i.
Arguments fp_compare_arrow {C P Q} D E i.
Arguments fp_compare_iso {C P Q} D E i.
Arguments fp_compare_iso_hom {C P Q} D E i.
Arguments fp_compare_left {C P Q} D E i.
Arguments fp_compare_right {C P Q} D E i.

Lemma fp_compare_index_cancel {C : category} {P Q : C}
    (D E : @finite_product_decomposition C P Q) :
    cancel (fp_compare_index D E) (fp_compare_index E D).
Proof.
move=> i; apply: (@fp_compare_index_unique C P Q E D _ _ (iso_symm (fp_compare_iso D E i))).
- rewrite -(@fp_compare_left C P Q D E i) -fp_compare_iso_hom -compose_assoc.
  by rewrite iso_inv_hom compose_id_left.
- rewrite -(@fp_compare_right C P Q D E i) -fp_compare_iso_hom -compose_assoc.
  by rewrite iso_inv_hom compose_id_left.
Qed.

Lemma fp_compare_index_bijective {C : category} {P Q : C}
    (D E : @finite_product_decomposition C P Q) : bijective (fp_compare_index D E).
Proof. exists (fp_compare_index E D); exact: fp_compare_index_cancel. Qed.

Print Assumptions fp_compare_iso.
Print Assumptions fp_compare_index_bijective.
