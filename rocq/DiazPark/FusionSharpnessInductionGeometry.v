(** Actual smaller saturated fusion system for the whole-E induction. *)
From mathcomp Require Import all_boot all_fingroup center pgroup abelian.
From DiazPark Require Import InductionOrder FiniteGroupInduction FusionSystems FusionSaturation
  FusionCentralizer FusionCentralizerMaps FusionCentralizerCentral FusionCentralizerSaturation
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientSaturation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionSharpnessInductionGeometry.
Section Geometry.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Hypothesis abE : abelian E.
Local Notation T := [subg 'C(E)%G]%type.
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation Z := (DPFusionCentralizerCentral.embedded E).

Definition quotient_type : finGroupType := [the finGroupType of coset_of Z].
Definition quotient_system : DPFusionSystem.system quotient_type :=
  DPFusionQuotientConstruction.system (DPFusionCentralizerCentral.embedded_central F abE).

Lemma embedded_card : #|Z| = #|E|.
Proof. exact (card_injm (injm_subg _) abE). Qed.
Lemma embedded_nontrivial : E :!=: 1%G -> Z :!=: 1%G.
Proof.
rewrite !trivg_card1 embedded_card; by [].
Qed.
Lemma embedded_normal : Z <| [set: T].
Proof. exact: sub_center_normal (DPFusionCentralizerCentral.embedded_sub_center abE). Qed.

Lemma quotient_carrier_card : #|quotient_type| = (#|'C(E)| %/ #|E|)%N.
Proof.
rewrite /quotient_type -(@cardsT [the finType of coset_of Z]).
rewrite -quotientT -(divg_normal embedded_normal) embedded_card.
by rewrite cardsT card_sub.
Qed.

Lemma quotient_carrier_lt : E :!=: 1%G -> (#|quotient_type| < #|S|)%N.
Proof.
move=> ntE.
have h := quotient_order_lt_ambient (embedded_nontrivial ntE) embedded_normal
  (subsetT [set: T]).
rewrite quotientT cardsT in h.
apply: leq_trans h _.
change (#|[set: T]| <= #|S|)%N.
rewrite cardsT card_sub -cardsT.
exact: subset_leq_card (subsetT 'C(E)).
Qed.

Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Hypothesis hE : DPFusionSystem.fully_centralized F E.

Lemma quotient_pgroup : p.-group [set: quotient_type].
Proof.
exact: DPFusionQuotientSaturation.quotient_pgroup
  (DPFusionCentralizerSaturation.centralizer_pgroup E pS).
Qed.
Lemma quotient_saturated : DPFusionSaturation.saturated quotient_system p.
Proof.
apply: DPFusionQuotientSaturation.central_quotient_saturated.
- exact (DPFusionCentralizerSaturation.centralizer_pgroup E pS).
- exact (DPFusionCentralizerSaturation.centralizer_saturated abE pS sat hE).
Qed.

Theorem smaller_saturated_quotient (ntE : E :!=: 1%G) :
  (#|quotient_type| < #|S|)%N /\ p.-group [set: quotient_type] /\
  DPFusionSaturation.saturated quotient_system p.
Proof. split; first exact: quotient_carrier_lt. split; [exact: quotient_pgroup | exact: quotient_saturated]. Qed.
End Geometry.

(** Ordinary strong induction on the cardinality of the actual carrier. *)
Theorem saturated_fusion_order_induction (p : nat)
    (Target : forall S : finGroupType, DPFusionSystem.system S -> Prop)
    (step : forall (S : finGroupType) (F : DPFusionSystem.system S),
      p.-group [set: S] -> DPFusionSaturation.saturated F p ->
      (forall (T : finGroupType) (G : DPFusionSystem.system T),
        (#|T| < #|S|)%N -> p.-group [set: T] ->
        DPFusionSaturation.saturated G p -> Target T G) -> Target S F) :
    forall (S : finGroupType) (F : DPFusionSystem.system S),
      p.-group [set: S] -> DPFusionSaturation.saturated F p -> Target S F.
Proof.
apply: (@finite_group_type_order_induction
  (fun S => forall F : DPFusionSystem.system S,
    p.-group [set: S] -> DPFusionSaturation.saturated F p -> Target S F)).
move=> S IH F pS sat; apply: step pS sat _.
move=> T G ltTS pT satG; exact: IH ltTS G pT satG.
Qed.
End DPFusionSharpnessInductionGeometry.







