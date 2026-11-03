(** Actual right-coset tower reindexing in a finite ambient group. *)
From mathcomp Require Import all_boot all_fingroup.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPGroupCohomologyCosetSums.
Section Cosets.
Variable G : finGroupType.

Definition coset_type (H K : {group G}) : finType :=
  [the finType of {C : {set G} | C \in rcosets H K}].

Lemma coset_representative (H K : {group G}) (C : coset_type H K) :
  H :* repr (val C) = val C.
Proof.
have /rcosetsP[x Kx hx] := valP C; rewrite hx; exact: rcoset_repr.
Qed.

Lemma coset_representative_mem (H K : {group G}) (hHK : H \subset K)
    (C : coset_type H K) : repr (val C) \in K.
Proof.
have /rcosetsP[x Kx hx] := valP C; rewrite hx.
have /rcosetP[h Hh ->] := mem_repr_rcoset H x.
exact: groupM (subsetP hHK _ Hh) Kx.
Qed.

Lemma coset_coarsen (P Q : {group G}) (hPQ : P \subset Q) (x y : G) :
  P :* x = P :* y -> Q :* x = Q :* y.
Proof.
move=> h; apply/rcoset_eqP.
have hx : x \in P :* y by rewrite -h rcoset_refl.
move: hx; rewrite !mem_rcoset=> hx; exact: (subsetP hPQ _ hx).
Qed.

Variables P Q T : {group G}.
Hypotheses (hPQ : P \subset Q) (hQT : Q \subset T).

Lemma tower_product_mem (V : coset_type Q T) (U : coset_type P Q) :
  val U :* repr (val V) \in rcosets P T.
Proof.
rewrite -(coset_representative U) -rcosetM.
apply/rcosetsP; exists (repr (val U) * repr (val V)); last reflexivity.
apply: groupM.
- exact: subsetP hQT _ (coset_representative_mem hPQ U).
- exact: coset_representative_mem hQT V.
Qed.

Definition tower_map (a : coset_type Q T * coset_type P Q) : coset_type P T :=
  Sub (val a.2 :* repr (val a.1)) (tower_product_mem a.1 a.2).

Lemma tower_map_value (a : coset_type Q T * coset_type P Q) :
  val (tower_map a) = val a.2 :* repr (val a.1).
Proof. reflexivity. Qed.

Theorem tower_map_injective : injective tower_map.
Proof.
move=> [V U] [V' U'] he.
have hh := congr1 val he.
change (val U :* repr (val V) = val U' :* repr (val V')) in hh.
have hsmall : P :* (repr (val U) * repr (val V)) =
    P :* (repr (val U') * repr (val V')).
  by rewrite !rcosetM !coset_representative.
have hlarge := coset_coarsen hPQ hsmall.
rewrite !rcosetM (rcoset_id (coset_representative_mem hPQ U))
  (rcoset_id (coset_representative_mem hPQ U')) !coset_representative in hlarge.
have hv : V = V' := val_inj hlarge; subst V'.
have hu : U = U' := val_inj (rcoset_inj hh).
by subst U'.
Qed.

Theorem tower_map_bijective : bijective tower_map.
Proof.
apply: inj_card_bij tower_map_injective _.
rewrite card_prod !card_sub.
rewrite (Lagrange_index hQT hPQ); exact: leqnn.
Qed.

End Cosets.
End DPGroupCohomologyCosetSums.

Print Assumptions DPGroupCohomologyCosetSums.tower_map_bijective.
