From mathcomp Require Import all_ssreflect fingroup perm morphism automorphism.
From mathcomp Require Import quotient cyclic pgroup sylow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** Automorphisms fixing a subgroup and acting trivially modulo it.
    These statements allow the subgroup to be trivial and do not require
    it to have exponent p.  All automorphism groups are actual MathComp
    subgroups of the permutation group. *)
Section AutomorphismDisplacement.

Variable gT : finGroupType.
Variables P Z : {group gT}.
Variable A : {group {perm gT}}.
Hypotheses (sAP : A \subset Aut P) (sZP : Z \subset P).
Hypothesis fixesZ : forall a, a \in A -> {in Z, a =1 id}.
Hypothesis displacementZ :
  forall a, a \in A -> forall x, x \in P -> x^-1 * a x \in Z.

Lemma automorphism_displacement_iter a (aA : a \in A) x (xP : x \in P) n :
  (a ^+ n) x = x * (x^-1 * a x) ^+ n.
Proof.
have aAut : a \in Aut P := subsetP sAP a aA.
have dZ := displacementZ aA xP.
have dP : x^-1 * a x \in P := subsetP sZP _ dZ.
have ad : a (x^-1 * a x) = x^-1 * a x := fixesZ aA dZ.
have ax : a x = x * (x^-1 * a x) by rewrite mulgA mulgV mul1g.
elim: n => [|n IHn]; first by rewrite !expg0 perm1 mulg1.
rewrite expgS permM {1}ax.
have anAut : a ^+ n \in Aut P := groupX n aAut.
rewrite (morphicP (Aut_morphic anAut)) // IHn (permX_fix n ad).
by rewrite -mulgA -expgSr.
Qed.

Lemma automorphism_displacement_power a (aA : a \in A) :
  a ^+ #|Z| = 1.
Proof.
have aAut : a \in Aut P := subsetP sAP a aA.
apply: (eq_Aut (groupX #|Z| aAut) (group1 _)).
move=> x xP; rewrite perm1 (automorphism_displacement_iter aA xP).
by rewrite (expg_cardG (displacementZ aA xP)) mulg1.
Qed.

Lemma automorphism_displacement_order a (aA : a \in A) :
  #[a] %| #|Z|.
Proof. by rewrite order_dvdn automorphism_displacement_power. Qed.

Lemma automorphism_displacement_pgroup (pi : nat_pred) :
  pi.-group Z -> pi.-group A.
Proof.
move/pgroupP=> piZ; apply/pgroupP=> q qpr qA.
have [a aA oa] := Cauchy qpr qA.
apply: (piZ q qpr).
by rewrite -oa automorphism_displacement_order.
Qed.

End AutomorphismDisplacement.

(** A normal p-subgroup is contained in every Sylow p-subgroup.
    This wrapper records the precise library facts used for the
    automorphism kernel of a central quotient. *)
Section NormalSubgroupSylow.
Variable gT : finGroupType.
Variables G K U : {group gT}.
Variable p : nat.

Lemma normal_pgroup_sub_sylow :
  K <| G -> p.-group K -> p.-Sylow(G) U -> K \subset U.
Proof.
move=> nKG pK sylU.
exact: normal_sub_max_pgroup (Hall_max sylU) pK nKG.
Qed.

End NormalSubgroupSylow.
