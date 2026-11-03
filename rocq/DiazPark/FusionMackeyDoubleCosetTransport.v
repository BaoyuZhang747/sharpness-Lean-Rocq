From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMackeyShape.
Import DPFusionMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPMackeyDoubleCosetTransport.
Section Translation.
Variable S : finGroupType.
Variables P Q T A B : {group S}.
Variables a b : S.
Hypotheses (aT : a \in T) (bT : b \in T).
Hypotheses (eA : A = (P :^ a)%G) (eB : B = (Q :^ b)%G).

Definition translate x := a^-1 * x * b.
Definition untranslate x := a * x * b^-1.
Lemma translate_cancel : cancel translate untranslate.
Proof. by move=> x; rewrite /translate /untranslate !mulgA mulgK mulgV mul1g. Qed.
Lemma untranslate_cancel : cancel untranslate translate.
Proof. by move=> x; rewrite /translate /untranslate !mulgA mulgKV mulVg mul1g. Qed.

Lemma translate_product h t k :
  translate (h * t * k) = h ^ a * translate t * k ^ b.
Proof. by rewrite /translate !conjgE !mulgA ?mulgK ?mulgKV. Qed.

Lemma translate_double_coset t :
  translate @: double_coset P Q t = double_coset A B (translate t).
Proof.
rewrite eA eB; apply/setP=> x; apply/imsetP/double_cosetP.
- move=> [y /double_cosetP[h [k [hP [kQ ->]]]] ->].
  exists (h ^ a), (k ^ b); split; first by rewrite mem_conjg conjgK.
  split; first by rewrite mem_conjg conjgK.
  exact: translate_product.
- move=> [h [k [hA [kB ->]]]].
  have hP : h ^ a^-1 \in P by move: hA; rewrite mem_conjg.
  have kQ : k ^ b^-1 \in Q by move: kB; rewrite mem_conjg.
  exists (h ^ a^-1 * t * k ^ b^-1).
  + apply/double_cosetP; by exists (h ^ a^-1), (k ^ b^-1).
  + by rewrite translate_product !conjgKV.
Qed.

Lemma translated_index_mem (i : double_coset_index P Q T) :
  translate @: val i \in double_coset A B @: T.
Proof.
apply/imsetP; exists (translate (double_coset_representative i)).
- rewrite /translate; apply: groupM=> //; apply: groupM.
  + by rewrite groupV.
  + exact: double_coset_representative_mem.
- by rewrite -translate_double_coset double_coset_representative_set.
Qed.
Definition translated_index (i : double_coset_index P Q T) : double_coset_index A B T :=
  Sub (translate @: val i) (translated_index_mem i).

Lemma translated_index_injective : injective translated_index.
Proof.
move=> i j h; apply: val_inj.
have he := congr1 (fun z : double_coset_index A B T => val z) h.
exact: (imset_inj (can_inj translate_cancel) he).
Qed.

Lemma translated_index_surjective j : exists i, translated_index i = j.
Proof.
pose t := double_coset_representative j.
have ht : t \in T := double_coset_representative_mem j.
have hu : untranslate t \in T.
  rewrite /untranslate; apply: groupM; first exact: groupM aT ht.
  by rewrite groupV.
have hi : double_coset P Q (untranslate t) \in double_coset P Q @: T.
  apply/imsetP; by exists (untranslate t).
exists (Sub (double_coset P Q (untranslate t)) hi); apply: val_inj.
change (translate @: double_coset P Q (untranslate t) = val j).
rewrite translate_double_coset untranslate_cancel; exact: double_coset_representative_set.
Qed.

Lemma untranslated_index_exists j : exists i, translated_index i == j.
Proof. by have [i hi] := translated_index_surjective j; exists i; rewrite hi. Qed.
Definition untranslated_index j := xchoose (untranslated_index_exists j).
Lemma translated_untranslated j : translated_index (untranslated_index j) = j.
Proof. exact: eqP (xchooseP (untranslated_index_exists j)). Qed.
Lemma untranslated_translated i : untranslated_index (translated_index i) = i.
Proof. apply: translated_index_injective; exact: translated_untranslated. Qed.
Lemma translated_index_bijective : bijective translated_index.
Proof. exists untranslated_index; [exact: untranslated_translated | exact: translated_untranslated]. Qed.

Lemma untranslated_representative i :
  double_coset P Q (untranslate (double_coset_representative (translated_index i))) =
  double_coset P Q (double_coset_representative i).
Proof.
apply: (imset_inj (can_inj translate_cancel)).
rewrite !translate_double_coset untranslate_cancel double_coset_representative_set /=.
by rewrite -translate_double_coset double_coset_representative_set.
Qed.

Lemma translated_apex t :
  (inclusion_apex A B t) :^ a^-1 = inclusion_apex P Q (untranslate t).
Proof.
by rewrite eA eB /inclusion_apex /untranslate conjIg conjsgK -!conjsgM !invgM invgK !mulgA.
Qed.
End Translation.
End DPMackeyDoubleCosetTransport.
