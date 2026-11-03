From mathcomp Require Import all_ssreflect all_fingroup center pgroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPTraceCentralizer.
Section CentralizerProduct.
Variable S : finGroupType.
Variables H T : {group S}.

Definition product : {group S} := (H <*> (T :&: 'C(H)))%G.

Lemma productE : product = H * (T :&: 'C(H)) :> {set S}.
Proof. exact: cent_joinEr (subsetIr _ _). Qed.

Lemma subgroup_sub_product : H \subset product.
Proof. exact: joing_subl. Qed.

Lemma centralizer_sub_product : T :&: 'C(H) \subset product.
Proof. exact: joing_subr. Qed.

Lemma product_sub_normalizer : product \subset 'N(H).
Proof.
rewrite /product join_subG normG /=.
exact: subset_trans (subsetIr _ _) (cent_sub H).
Qed.

Lemma subgroup_normal_product : H <| product.
Proof. by rewrite /normal subgroup_sub_product product_sub_normalizer. Qed.

Lemma product_sub_ambient : H \subset T -> product \subset T.
Proof. by move=> sHT; rewrite /product join_subG sHT subsetIl. Qed.

Lemma product_sub_relative_normalizer :
  H \subset T -> product \subset 'N(H) :&: T.
Proof. by move=> sHT; rewrite subsetI product_sub_normalizer product_sub_ambient. Qed.

Lemma product_conjugation_inner d :
  d \in product -> exists h, h \in H /\ {in H, (fun x => x ^ d) =1 (fun x => x ^ h)}.
Proof.
rewrite productE => /mulsgP[h c hH /setIP[cT cC] ->].
exists h; split=> // x xH.
rewrite conjgM; apply/conjg_fixP/commgP.
exact: esym (centP cC _ (groupJ xH hH)).
Qed.

Lemma subgroup_proper_product :
  ~~ (T :&: 'C(H) \subset H) -> H \proper product.
Proof.
move=> ncH; rewrite properE subgroup_sub_product /=.
apply/negP=> sDH.
have sCH := subset_trans centralizer_sub_product sDH.
by move: ncH; rewrite sCH.
Qed.

Lemma quotient_nontrivial :
  ~~ (T :&: 'C(H) \subset H) -> (product / H) :!=: 1.
Proof. by rewrite quotient_neq1 ?subgroup_normal_product //; apply: subgroup_proper_product. Qed.

Lemma quotient_sub_normalizer_quotient :
  H \subset T -> product / H \subset ('N(H) :&: T) / H.
Proof. move=> sHT; exact: quotientS (product_sub_relative_normalizer sHT). Qed.

Lemma quotient_pgroup (p : nat) :
  H \subset T -> p.-group T -> p.-group (product / H).
Proof.
move=> sHT pT.
exact: quotient_pgroup (pgroupS (product_sub_ambient sHT) pT).
Qed.

Lemma quotient_card_divisible (p : nat) :
  H \subset T -> p.-group T -> ~~ (T :&: 'C(H) \subset H) ->
  p %| #|product / H|.
Proof.
move=> sHT pT ncH.
have [_ hp _] := pgroup_pdiv (quotient_pgroup sHT pT) (quotient_nontrivial ncH).
exact: hp.
Qed.

Lemma quotient_card_gt_one :
  ~~ (T :&: 'C(H) \subset H) -> (1 < #|product / H|)%N.
Proof. by rewrite cardG_gt1; apply: quotient_nontrivial. Qed.

End CentralizerProduct.
End DPTraceCentralizer.

Print Assumptions DPTraceCentralizer.productE.
Print Assumptions DPTraceCentralizer.subgroup_normal_product.
Print Assumptions DPTraceCentralizer.product_sub_relative_normalizer.
Print Assumptions DPTraceCentralizer.product_conjugation_inner.
Print Assumptions DPTraceCentralizer.quotient_nontrivial.
Print Assumptions DPTraceCentralizer.quotient_pgroup.
Print Assumptions DPTraceCentralizer.quotient_card_divisible.
Print Assumptions DPTraceCentralizer.quotient_card_gt_one.
