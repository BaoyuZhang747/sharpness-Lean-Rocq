(** Literal nonempty strict chains of F-centric subgroups.  Finiteness is
    obtained from the proved length bound, not a chosen truncation. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPLinkingChains.
Section Chains.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition strict_entries n (c : {ffun 'I_n.+1 -> Obj}) : bool :=
  [forall i : 'I_n.+1, [forall j : 'I_n.+1, (i < j) ==> (val (c i) \proper val (c j))]].

Lemma strict_entriesP n (c : {ffun 'I_n.+1 -> Obj}) :
  reflect (forall i j : 'I_n.+1, i < j -> val (c i) \proper val (c j)) (strict_entries c).
Proof.
apply: (iffP forallP).
- move=> h i j hij; exact: (implyP (forallP (h i) j) hij).
- move=> h i; apply/forallP=> j; apply/implyP; exact: h.
Qed.

Lemma strict_entries_injective n (c : {ffun 'I_n.+1 -> Obj}) :
  strict_entries c -> injective c.
Proof.
move/strict_entriesP=> hc i j he.
have hn (a b : 'I_n.+1) : a < b -> c a != c b.
  move=> hab; apply/eqP=> eqab.
  have hneq := proper_neq (hc a b hab).
  by rewrite eqab eqxx in hneq.
case: (ltngtP (val i) (val j))=> hij.
- have := hn i j hij; by rewrite he eqxx.
- have := hn j i hij; by rewrite he eqxx.
- exact: val_inj hij.
Qed.

Theorem strict_entries_length_bound n (c : {ffun 'I_n.+1 -> Obj}) :
  strict_entries c -> n < #|{: Obj}|.
Proof.
move=> hc; have hb := leq_card c (strict_entries_injective hc).
by rewrite card_ord in hb.
Qed.

Definition chain_at n := {c : {ffun 'I_n.+1 -> Obj} | strict_entries c}.
Definition chain : finType :=
  [the finType of {n : 'I_(#|{: Obj}|) & chain_at n}].

Definition length (c : chain) : nat := val (projT1 c).
Definition entry (c : chain) : 'I_(length c).+1 -> Obj := val (projT2 c).
Arguments entry c i : clear implicits.
Definition subgroup (c : chain) (i : 'I_(length c).+1) : {group S} := val (entry c i).
Arguments subgroup c i : clear implicits.

Lemma entry_strict (c : chain) (i j : 'I_(length c).+1) :
  i < j -> subgroup c i \proper subgroup c j.
Proof.
have /strict_entriesP hc := valP (projT2 c).
exact: hc.
Qed.

Lemma entry_mono (c : chain) (i j : 'I_(length c).+1) :
  i <= j -> subgroup c i \subset subgroup c j.
Proof.
rewrite leq_eqVlt; move/orP=> [/eqP hij|hij].
- have -> : i = j := val_inj hij; exact: subxx.
- exact: proper_sub (entry_strict hij).
Qed.

Lemma entry_injective (c : chain) : injective (entry c).
Proof. exact: strict_entries_injective (valP (projT2 c)). Qed.

Definition of_entries n (c : {ffun 'I_n.+1 -> Obj}) (hc : strict_entries c) : chain :=
  existT (fun n : 'I_(#|{: Obj}|) => chain_at n)
    (Ordinal (strict_entries_length_bound hc)) (Sub c hc).

Lemma of_entries_length n (c : {ffun 'I_n.+1 -> Obj}) (hc : strict_entries c) :
  length (of_entries hc) = n.
Proof. reflexivity. Qed.

Lemma of_entries_entry n (c : {ffun 'I_n.+1 -> Obj}) (hc : strict_entries c) i :
  entry (of_entries hc) i = c i.
Proof. reflexivity. Qed.

Lemma singleton_strict (P : Obj) : strict_entries [ffun _ : 'I_1 => P].
Proof.
apply/strict_entriesP=> i j; rewrite (ord1 i) (ord1 j) ltnn; by [].
Qed.

Definition singleton (P : Obj) : chain := of_entries (singleton_strict P).

Lemma singleton_length (P : Obj) : length (singleton P) = 0.
Proof. reflexivity. Qed.

Lemma singleton_entry (P : Obj) i : entry (singleton P) i = P.
Proof. exact: ffunE. Qed.

Definition bottom (c : chain) : Obj := entry c ord0.
Definition top (c : chain) : Obj := entry c ord_max.

Lemma entry_sub_top (c : chain) (i : 'I_(length c).+1) :
  subgroup c i \subset val (top c).
Proof. apply: entry_mono; exact: leq_ord. Qed.

Definition subchain (c : chain) m (e : 'I_m.+1 -> 'I_(length c).+1)
    (he : forall i j : 'I_m.+1, i < j -> e i < e j) : chain.
Proof.
apply: (@of_entries m [ffun i => entry c (e i)]).
apply/strict_entriesP=> i j hij; rewrite !ffunE.
exact: entry_strict (he i j hij).
Defined.

Lemma subchain_length (c : chain) m e he : length (@subchain c m e he) = m.
Proof. reflexivity. Qed.

Lemma subchain_entry (c : chain) m e he i :
  entry (@subchain c m e he) i = entry c (e i).
Proof. exact: ffunE. Qed.

End Chains.
Arguments entry {S F} c i.
Arguments subgroup {S F} c i.
End DPLinkingChains.

Check DPLinkingChains.chain.
Print Assumptions DPLinkingChains.strict_entries_length_bound.
Print Assumptions DPLinkingChains.of_entries.



