(** Actual subgroup and centre carriers under the subgroup embedding sgval.
    The maps retain their literal element values and commute with the
    distinguished inclusion of a centre into its subgroup. *)
From mathcomp Require Import all_boot all_fingroup center.
From DiazPark Require Import FusionCentralizerMaps.
From DiazParkV16b Require Import LinkingSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionSubgroup.
Local Open Scope group_scope.

Module DPBLOCenterElements.
Section SubgroupCarriers.
Variable S : finGroupType.
Variable C : {group S}.
Local Notation T := [subg C]%type.
Variable P : {group T}.

Definition subgroup_up (x : [subg P]) : [subg (ambient P)] :=
  Sub (val (val x)) (ambient_mem (valP x)).

Definition subgroup_down (x : [subg (ambient P)]) : [subg P] :=
  Sub (subg C (val x)) (ambient_repr (valP x)).

Lemma subgroup_up_value (x : [subg P]) :
  val (subgroup_up x) = val (val x).
Proof. reflexivity. Qed.

Lemma subgroup_down_value (x : [subg (ambient P)]) :
  val (subgroup_down x) = subg C (val x).
Proof. reflexivity. Qed.

Lemma subgroup_down_ambient_value (x : [subg (ambient P)]) :
  val (val (subgroup_down x)) = val x.
Proof. exact: ambient_subgK (valP x). Qed.

Lemma subgroup_upK : cancel subgroup_up subgroup_down.
Proof. move=> x; apply: val_inj; exact: sgvalK. Qed.

Lemma subgroup_downK : cancel subgroup_down subgroup_up.
Proof. move=> x; apply: val_inj; exact: ambient_subgK (valP x). Qed.

Lemma subgroup_up_bijective : bijective subgroup_up.
Proof. exists subgroup_down; [exact: subgroup_upK | exact: subgroup_downK]. Qed.

Lemma centre_up_mem (z : [subg 'Z(P)]) :
  val (val z) \in 'Z(ambient P).
Proof.
have hz := setIP (valP z).
apply/setIP; split; first exact: ambient_mem hz.1.
apply/centP=> y /morphimP[x _ Px ->].
exact (congr1 (fun t : T => val t) ((centP hz.2) x Px)).
Qed.

Definition centre_up (z : [subg 'Z(P)]) : [subg 'Z(ambient P)] :=
  Sub (val (val z)) (centre_up_mem z).

Lemma centre_down_mem (z : [subg 'Z(ambient P)]) :
  subg C (val z) \in 'Z(P).
Proof.
have hz := setIP (valP z).
apply/setIP; split; first exact: ambient_repr hz.1.
apply/centP=> y Py; apply: val_inj.
change (val (subg C (val z)) * val y = val y * val (subg C (val z))).
rewrite (ambient_subgK hz.1).
exact ((centP hz.2) (val y) (ambient_mem Py)).
Qed.

Definition centre_down (z : [subg 'Z(ambient P)]) : [subg 'Z(P)] :=
  Sub (subg C (val z)) (centre_down_mem z).

Lemma centre_up_value (z : [subg 'Z(P)]) :
  val (centre_up z) = val (val z).
Proof. reflexivity. Qed.

Lemma centre_down_value (z : [subg 'Z(ambient P)]) :
  val (centre_down z) = subg C (val z).
Proof. reflexivity. Qed.

Lemma centre_down_ambient_value (z : [subg 'Z(ambient P)]) :
  val (val (centre_down z)) = val z.
Proof. exact: ambient_subgK (subsetP (center_sub _) _ (valP z)). Qed.

Lemma centre_upK : cancel centre_up centre_down.
Proof. move=> z; apply: val_inj; exact: sgvalK. Qed.

Lemma centre_downK : cancel centre_down centre_up.
Proof.
move=> z; apply: val_inj.
exact: ambient_subgK (subsetP (center_sub _) _ (valP z)).
Qed.

Lemma centre_up_bijective : bijective centre_up.
Proof. exists centre_down; [exact: centre_upK | exact: centre_downK]. Qed.

Lemma centre_up_mul (x y : [subg 'Z(P)]) :
  centre_up (x * y) = centre_up x * centre_up y.
Proof. by apply: val_inj. Qed.

Lemma centre_up_one : centre_up 1 = 1.
Proof. by apply: val_inj. Qed.

Lemma centre_up_inclusion (z : [subg 'Z(P)]) :
  subgroup_up (DPCentricLinking.center_element z) =
    DPCentricLinking.center_element (centre_up z).
Proof. by apply: val_inj. Qed.

End SubgroupCarriers.
End DPBLOCenterElements.
