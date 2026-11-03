From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMackeyShape.

(** The actual self-intersection test in the Mackey sum. A full-size
    intersection is equivalent to membership in the normalizer. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Import DPFusionMackey.

Section SelfDoubleCosets.
Variable S : finGroupType.
Variable H : {group S}.

Lemma trace_self_apex_normalizer t :
    (inclusion_apex H H t == H) = (t \in 'N(H)).
Proof.
apply/eqP/idP.
- move=> hA.
  have hsub : H \subset H :^ t^-1.
    rewrite -{1}hA; exact: subsetIr.
  have hc : H :^ t^-1 = H.
    symmetry; apply/eqP; by rewrite eqEcard cardJg leqnn andbT.
  have hn : t^-1 \in 'N(H) by apply/normP.
  by move: hn; rewrite groupV.
- move=> hn.
  have hnv : t^-1 \in 'N(H) by rewrite groupV.
  apply: val_inj; by rewrite /inclusion_apex /= (normP hnv) setIid.
Qed.

Lemma trace_self_apex_card_lt t : t \notin 'N(H) ->
    (#|inclusion_apex H H t| < #|H|)%N.
Proof.
move=> hn.
have hs : inclusion_apex H H t \subset H := subsetIl _ _.
have hp : inclusion_apex H H t \proper H.
  rewrite properEneq hs andbT; apply/negP=> /eqP he.
  have heG : inclusion_apex H H t = H := val_inj he.
  have ht : t \in 'N(H) by rewrite -trace_self_apex_normalizer heG eqxx.
  by move: hn; rewrite ht.
exact: proper_card hp.
Qed.

Lemma trace_normalizing_double_coset t : t \in 'N(H) ->
    double_coset H H t = H :* t.
Proof.
move=> hn.
have hs : [set t] \subset 'N(H) by rewrite sub1set.
by rewrite /double_coset -mulgA (normC hs) mulgA mulGid.
Qed.

End SelfDoubleCosets.

Section Membership.
Variable S : finGroupType.
Variables H K T : {group S}.

Lemma trace_double_coset_contains_representative t : t \in double_coset H K t.
Proof.
apply/double_cosetP; exists 1, 1; split; first exact: group1.
split; first exact: group1. by rewrite mul1g mulg1.
Qed.

Lemma trace_double_coset_chosen_mem (i : double_coset_index H K T) :
    double_coset_representative i \in val i.
Proof.
rewrite -(double_coset_representative_set i).
exact: trace_double_coset_contains_representative.
Qed.

End Membership.

Section SurvivingCosets.
Variable S : finGroupType.
Variables H T : {group S}.

Definition trace_normalizer : {group S} := ('N(H) :&: T)%G.
Definition trace_survivor :=
  {i : double_coset_index H H T | double_coset_representative i \in 'N(H)}.
Definition trace_normalizer_coset := {X : {set S} | X \in rcosets H trace_normalizer}.

Lemma trace_survivor_is_coset (i : trace_survivor) :
    val (val i) \in rcosets H trace_normalizer.
Proof.
apply/rcosetsP; exists (double_coset_representative (val i)).
- apply/setIP; split; [exact: valP i | exact: double_coset_representative_mem].
- by rewrite -(double_coset_representative_set (val i)) trace_normalizing_double_coset ?(valP i).
Qed.

Definition trace_survivor_to_coset (i : trace_survivor) : trace_normalizer_coset :=
  Sub (val (val i)) (trace_survivor_is_coset i).

Lemma trace_coset_is_double_coset (X : trace_normalizer_coset) :
    val X \in (double_coset H H) @: T.
Proof.
have /rcosetsP[t /setIP[Nt Tt] hX] := valP X.
apply/imsetP; exists t=> //.
by rewrite hX trace_normalizing_double_coset.
Qed.

Definition trace_coset_double_index (X : trace_normalizer_coset) :
    double_coset_index H H T := Sub (val X) (trace_coset_is_double_coset X).

Lemma trace_coset_representative_normalizes (X : trace_normalizer_coset) :
    double_coset_representative (trace_coset_double_index X) \in 'N(H).
Proof.
have hmem := trace_double_coset_chosen_mem (trace_coset_double_index X).
change (is_true (double_coset_representative (trace_coset_double_index X) \in val X)) in hmem.
have /rcosetsP[t /setIP[Nt Tt] hX] := valP X.
have hs : val X \subset 'N(H).
  rewrite hX; apply: mul_subG; first exact: normG.
  by rewrite sub1set.
exact: (subsetP hs _ hmem).
Qed.

Definition trace_coset_to_survivor (X : trace_normalizer_coset) : trace_survivor :=
  Sub (trace_coset_double_index X) (trace_coset_representative_normalizes X).

Lemma trace_survivor_coset_cancel : cancel trace_survivor_to_coset trace_coset_to_survivor.
Proof. move=> i; apply: val_inj; apply: val_inj; reflexivity. Qed.

Lemma trace_coset_survivor_cancel : cancel trace_coset_to_survivor trace_survivor_to_coset.
Proof. move=> X; apply: val_inj; reflexivity. Qed.

Lemma trace_survivor_coset_bijective : bijective trace_survivor_to_coset.
Proof. exists trace_coset_to_survivor; [exact: trace_survivor_coset_cancel | exact: trace_coset_survivor_cancel]. Qed.

Definition trace_quotient_element := {q : coset_of H | q \in trace_normalizer / H}.

Lemma trace_normalizer_quotient_sets :
    val @: (trace_normalizer / H) = rcosets H trace_normalizer.
Proof.
rewrite val_quotient; congr (rcosets H _).
apply/setIidPl; exact: subsetIl.
Qed.

Lemma trace_quotient_is_coset (q : trace_quotient_element) :
    val (val q) \in rcosets H trace_normalizer.
Proof.
rewrite -trace_normalizer_quotient_sets.
exact: imset_f (valP q).
Qed.

Definition trace_quotient_to_coset (q : trace_quotient_element) : trace_normalizer_coset :=
  Sub (val (val q)) (trace_quotient_is_coset q).

Lemma trace_coset_quotient_exists (X : trace_normalizer_coset) :
    exists q : coset_of H, (q \in trace_normalizer / H) && (val q == val X).
Proof.
have hx : val X \in val @: (trace_normalizer / H).
  rewrite trace_normalizer_quotient_sets; exact: valP X.
have /imsetP[q hq hxq] := hx.
by exists q; rewrite hq -hxq eqxx.
Qed.

Definition trace_coset_to_quotient (X : trace_normalizer_coset) : trace_quotient_element :=
  Sub (xchoose (trace_coset_quotient_exists X))
    (andP (xchooseP (trace_coset_quotient_exists X))).1.

Lemma trace_coset_to_quotient_set (X : trace_normalizer_coset) :
    val (val (trace_coset_to_quotient X)) = val X.
Proof. apply/eqP; exact: (andP (xchooseP (trace_coset_quotient_exists X))).2. Qed.

Lemma trace_quotient_coset_cancel : cancel trace_quotient_to_coset trace_coset_to_quotient.
Proof.
move=> q; apply: val_inj; apply: val_inj.
exact: trace_coset_to_quotient_set.
Qed.

Lemma trace_coset_quotient_cancel : cancel trace_coset_to_quotient trace_quotient_to_coset.
Proof. move=> X; apply: val_inj; exact: trace_coset_to_quotient_set. Qed.

Definition trace_survivor_to_quotient (i : trace_survivor) : trace_quotient_element :=
  trace_coset_to_quotient (trace_survivor_to_coset i).

Definition trace_quotient_to_survivor (q : trace_quotient_element) : trace_survivor :=
  trace_coset_to_survivor (trace_quotient_to_coset q).

Lemma trace_survivor_quotient_cancel : cancel trace_survivor_to_quotient trace_quotient_to_survivor.
Proof.
move=> i; rewrite /trace_survivor_to_quotient /trace_quotient_to_survivor
  trace_coset_quotient_cancel; exact: trace_survivor_coset_cancel.
Qed.

Lemma trace_quotient_survivor_cancel : cancel trace_quotient_to_survivor trace_survivor_to_quotient.
Proof.
move=> q; rewrite /trace_survivor_to_quotient /trace_quotient_to_survivor
  trace_coset_survivor_cancel; exact: trace_quotient_coset_cancel.
Qed.

Lemma trace_quotient_survivor_bijective : bijective trace_quotient_to_survivor.
Proof. exists trace_survivor_to_quotient; [exact: trace_quotient_survivor_cancel | exact: trace_survivor_quotient_cancel]. Qed.

Lemma trace_survivor_quotient_value (i : trace_survivor) :
    val (trace_survivor_to_quotient i) = coset H (double_coset_representative (val i)).
Proof.
apply: val_inj.
change ((val (trace_survivor_to_quotient i) : {set S}) =
  (coset H (double_coset_representative (val i)) : {set S})).
rewrite val_coset ?(valP i) //.
rewrite /trace_survivor_to_quotient trace_coset_to_quotient_set /=
  -(double_coset_representative_set (val i)).
exact: trace_normalizing_double_coset (valP i).
Qed.

End SurvivingCosets.

Print Assumptions trace_self_apex_normalizer.
Print Assumptions trace_self_apex_card_lt.
Print Assumptions trace_normalizing_double_coset.
Print Assumptions trace_survivor_coset_bijective.
Print Assumptions trace_quotient_survivor_bijective.
Print Assumptions trace_survivor_quotient_value.
