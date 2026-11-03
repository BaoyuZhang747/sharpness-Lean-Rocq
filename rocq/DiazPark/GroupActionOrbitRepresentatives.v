(** Actual orbit representatives with stabilizer in a fixed Sylow subgroup.
    Actions use a left-action convention, matching forward precomposition. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup pgroup sylow generic_quotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPLeftAction.
Section Action.
Variable G : finGroupType.
Variable X : finType.
Variable act : G -> X -> X.
Hypothesis act_one : forall x, act 1 x = x.
Hypothesis act_mul : forall g h x, act (g*h) x = act g (act h x).

Lemma act_cancel g x : act g^-1 (act g x) = x.
Proof. by rewrite -act_mul mulVg act_one. Qed.
Lemma act_injective g : injective (act g).
Proof. move=> x y h. by rewrite -(act_cancel g x) -(act_cancel g y) h. Qed.

Definition stabilizer_set x := [set g | act g x == x].
Lemma stabilizer_group x : group_set (stabilizer_set x).
Proof.
  apply/group_setP; split; first by rewrite inE act_one eqxx.
  move=> g h. rewrite !inE => /eqP hg /eqP hh.
  by rewrite act_mul hh hg eqxx.
Qed.
Definition stabilizer x : {group G} := group (stabilizer_group x).
Lemma stabilizerP x g : reflect (act g x = x) (g \in stabilizer x).
Proof. rewrite /stabilizer /stabilizer_set inE. exact: eqP. Qed.

Lemma stabilizer_translate g x : stabilizer (act g x) = (stabilizer x :^ g^-1)%G.
Proof.
  apply val_inj; apply/setP=> h.
  rewrite mem_conjg invgK.
  apply/stabilizerP/stabilizerP => hh.
  - apply (@act_injective g).
    by rewrite -!act_mul conjgE !mulgA mulgV mul1g act_mul hh.
  - apply (@act_injective g^-1).
    rewrite act_cancel -!act_mul.
    by rewrite -mulgA -conjgE.
Qed.

Definition related x y := [exists g : G, act g y == x].
Lemma related_refl : reflexive related.
Proof. move=> x. apply/existsP; exists 1. by rewrite act_one eqxx. Qed.
Lemma related_sym : symmetric related.
Proof.
  move=> x y. apply/idP/idP; move/existsP=> [g /eqP h];
    apply/existsP; exists g^-1; apply/eqP; by rewrite -h act_cancel.
Qed.
Lemma related_trans : transitive related.
Proof.
  move=> x y z /existsP[g /eqP hg] /existsP[h /eqP hh].
  apply/existsP; exists (g*h). apply/eqP. by rewrite act_mul hh hg.
Qed.
Definition orbit_relation := EquivRel related related_refl related_sym related_trans.
Definition orbit_index := {eq_quot orbit_relation}.
#[export] HB.instance Definition _ := [Finite of orbit_index by <:%/].
Definition orbit_class (x : X) : orbit_index := \pi_(orbit_index) x.
Lemma orbit_class_eq x y : reflect (orbit_class x = orbit_class y) (related x y).
Proof. exact: eqmodP. Qed.
Lemma orbit_class_translate g x : orbit_class (act g x) = orbit_class x.
Proof. apply/orbit_class_eq/existsP. exists g. exact: eqxx. Qed.

Variable p : nat.
Variable T : {group G}.
Hypothesis sylT : p.-Sylow([set: G]) T.
Hypothesis stabilizers_pgroup : forall x, p.-group (stabilizer x).

Definition conjugator (x : X) : {g : G | stabilizer x :^ g \subset T}.
Proof.
  have hex : exists g : G, stabilizer x :^ g \subset T.
    have [g _ hg] := Sylow_Jsub sylT (subsetT (stabilizer x)) (stabilizers_pgroup x).
    exact (ex_intro _ g hg).
  exact (sigW hex).
Defined.
Definition representative (i : orbit_index) := act (val (conjugator (repr i)))^-1 (repr i).
Lemma representative_class i : orbit_class (representative i) = i.
Proof. rewrite /representative orbit_class_translate. exact: reprK. Qed.
Lemma representative_stabilizer_sub i : stabilizer (representative i) \subset T.
Proof. rewrite /representative stabilizer_translate invgK. exact (valP (conjugator (repr i))). Qed.
Lemma representative_stabilizer_pgroup i : p.-group (stabilizer (representative i)).
Proof. exact: stabilizers_pgroup. Qed.
Lemma class_representative_related x : related x (representative (orbit_class x)).
Proof. apply/orbit_class_eq. by rewrite representative_class. Qed.

End Action.
End DPLeftAction.
