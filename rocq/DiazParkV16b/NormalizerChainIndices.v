(** Actual increasing selections of entries of finite nonempty strict chains. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains.

Module DPNormalizerChainIndices.
Section Indices.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition increasing (c d : chain F)
    (e : {ffun 'I_(length d).+1 -> 'I_(length c).+1}) :=
  [forall i : 'I_(length d).+1, [forall j : 'I_(length d).+1, (i < j) ==> (e i < e j)]].

Lemma increasingP (c d : chain F) (e : {ffun 'I_(length d).+1 -> 'I_(length c).+1}) : reflect
  (forall i j : 'I_(length d).+1, i < j -> e i < e j) (@increasing c d e).
Proof.
apply: (iffP forallP).
- move=> h i j hij; exact: implyP (forallP (h i) j) hij.
- move=> h i; apply/forallP=> j; apply/implyP; exact: h.
Qed.

Definition selector (c d : chain F) :=
  {e : {ffun 'I_(length d).+1 -> 'I_(length c).+1} | @increasing c d e}.

Definition index (c d : chain F) (e : selector c d) := val e.

Lemma index_strict (c d : chain F) (e : selector c d) (i j : 'I_(length d).+1) :
  i < j -> index e i < index e j.
Proof. exact (elimT (@increasingP c d (val e)) (valP e) i j). Qed.

Lemma index_mono (c d : chain F) (e : selector c d) (i j : 'I_(length d).+1) :
  i <= j -> index e i <= index e j.
Proof.
rewrite leq_eqVlt; move/orP=> [/eqP hij | hij].
- have -> : i = j := val_inj hij; exact: leqnn.
- exact: ltnW (index_strict e hij).
Qed.

Lemma index_injective (c d : chain F) (e : selector c d) : injective (index e).
Proof.
move=> i j he; case: (ltngtP (val i) (val j))=> hij.
- have h := index_strict e hij; by rewrite he ltnn in h.
- have h := index_strict e hij; by rewrite he ltnn in h.
- exact: val_inj hij.
Qed.

Lemma selector_length (c d : chain F) (e : selector c d) : length d <= length c.
Proof.
have h := leq_card (index e) (@index_injective c d e).
by rewrite !card_ord ltnS in h.
Qed.

Lemma equal_length_bijective (c d : chain F) (e : selector c d) :
  length c = length d -> bijective (index e).
Proof.
move=> he; apply: inj_card_bij (@index_injective c d e) _.
by rewrite !card_ord he.
Qed.

Definition identity (c : chain F) : selector c c.
Proof.
apply: (Sub [ffun i => i]); apply/increasingP=> i j hij; by rewrite !ffunE.
Defined.

Lemma identity_index (c : chain F) i : index (identity c) i = i.
Proof. exact: ffunE. Qed.

Definition compose (c d t : chain F) (a : selector c d) (b : selector d t) : selector c t.
Proof.
apply: (Sub [ffun i => index a (index b i)]); apply/increasingP=> i j hij.
rewrite !ffunE; exact (@index_strict c d a _ _ (@index_strict d t b i j hij)).
Defined.

Lemma compose_index (c d t : chain F) (a : selector c d) (b : selector d t) i :
  index (compose a b) i = index a (index b i).
Proof. exact: ffunE. Qed.

Definition selected_chain (c d : chain F) (e : selector c d) : chain F :=
  @subchain S F c (length d) (index e) (@index_strict c d e).

Lemma selected_chain_length (c d : chain F) (e : selector c d) :
  length (selected_chain e) = length d.
Proof. reflexivity. Qed.

Lemma selected_chain_entry (c d : chain F) (e : selector c d) i :
  entry (selected_chain e) i = entry c (index e i).
Proof. exact: subchain_entry. Qed.

End Indices.
End DPNormalizerChainIndices.
