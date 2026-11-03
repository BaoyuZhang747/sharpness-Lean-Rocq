(** The native orbit-of-cosets index is exactly the canonical double-coset
    carrier index. Both use the same P\T/Q orientation. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import FusionMackeyShape.
From DiazParkV16b Require Import GroupCohomologyCosetSumsDoubleCosets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyCosetSumsDoubleCosets.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module DPGroupCohomologyMackeyDoubleCosetIndices.
Section Indices.
Variable G : finGroupType.
Variables P Q T : {group G}.
Hypotheses (hPT : P \subset T) (hQT : Q \subset T).
Definition native_index := {D : {set {set G}} | D \in double_cosets P Q T}.
Local Notation Canonical := (DPFusionMackey.double_coset_index P Q T).

Lemma coset_of_native D (hD : D \in double_cosets P Q T) C :
  C \in D -> C \in rcosets P T.
Proof.
move=> hC; have /imsetP[E hE he] := hD.
have hsub : D \subset rcosets P T by rewrite he (acts_sub_orbit E (right_cosets_action P hQT)).
exact: subsetP hsub _ hC.
Qed.

Lemma carrier_membership D (hD : D \in double_cosets P Q T) x :
  (x \in double_coset_carrier D) = (P :* x \in D).
Proof.
apply/idP/idP.
- move/bigcupP=> [C hC hx].
  have /rcosetsP[y hy hCy] := coset_of_native hD hC.
  rewrite hCy in hx; have /rcosetP[p hp hpx] := hx.
  rewrite hpx rcosetM (rcoset_id hp) -hCy; exact hC.
- move=> hx; apply/bigcupP; exists (P :* x)=> //.
  apply/rcosetP; exists 1; [exact: group1 | by rewrite mul1g].
Qed.

Lemma carrier_injective : injective (fun D : native_index => double_coset_carrier (val D)).
Proof.
move=> D E he; apply val_inj.
rewrite -(double_coset_orbit hQT (valP D)) -(double_coset_orbit hQT (valP E)).
apply: (elimT (@orbit_eqP G [the finType of {set G}] 'Rs Q _ _)).
rewrite (double_coset_orbit hQT (valP E)) -(carrier_membership (valP E)).
rewrite -he (carrier_membership (valP D)).
rewrite (chosen_coset_repr hQT (valP D)).
exact (chosen_coset_mem (valP D)).
Qed.

Lemma carrier_is_double_coset (D : native_index) :
  double_coset_carrier (val D) \in DPFusionMackey.double_coset P Q @: T.
Proof.
apply/imsetP; exists (double_coset_repr P (val D)).
- exact (@double_coset_repr_mem G P Q T hPT hQT (val D) (valP D)).
- exact (@double_coset_carrier_formula G P Q T hQT (val D) (valP D)).
Qed.

Definition to_canonical (D : native_index) : Canonical :=
  Sub (double_coset_carrier (val D)) (carrier_is_double_coset D).

Lemma to_canonical_value (D : native_index) :
  val (to_canonical D) = double_coset_carrier (val D).
Proof. reflexivity. Qed.

Lemma to_canonical_injective : injective to_canonical.
Proof. move=> D E he; apply carrier_injective; exact (congr1 val he). Qed.

Lemma canonical_orbit_mem (i : Canonical) :
  orbit 'Rs Q (P :* DPFusionMackey.double_coset_representative i) \in double_cosets P Q T.
Proof.
apply/imsetP; exists (P :* DPFusionMackey.double_coset_representative i)=> //.
apply/rcosetsP; exists (DPFusionMackey.double_coset_representative i)=> //.
exact: DPFusionMackey.double_coset_representative_mem.
Qed.

Definition from_canonical (i : Canonical) : native_index :=
  Sub (orbit 'Rs Q (P :* DPFusionMackey.double_coset_representative i))
    (canonical_orbit_mem i).

Lemma canonical_cancel : cancel from_canonical to_canonical.
Proof.
move=> i; apply val_inj.
change (double_coset_carrier (orbit 'Rs Q
  (P :* DPFusionMackey.double_coset_representative i)) = val i).
rewrite orbit_carrier; exact: DPFusionMackey.double_coset_representative_set.
Qed.

Lemma native_cancel : cancel to_canonical from_canonical.
Proof. move=> D; apply to_canonical_injective; exact: canonical_cancel. Qed.

Theorem to_canonical_bijective : bijective to_canonical.
Proof. exists from_canonical; [exact: native_cancel | exact: canonical_cancel]. Qed.

Lemma native_representative_set (D : native_index) :
  DPFusionMackey.double_coset P Q (double_coset_repr P (val D)) = val (to_canonical D).
Proof. symmetry; exact (@double_coset_carrier_formula G P Q T hQT (val D) (valP D)). Qed.

End Indices.
End DPGroupCohomologyMackeyDoubleCosetIndices.
