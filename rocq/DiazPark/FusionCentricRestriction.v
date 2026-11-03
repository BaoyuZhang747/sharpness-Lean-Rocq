From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup nilpotent sylow.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionCentricBasics FusionCentricRigidity.
Import DPFusion DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricRestriction.
Section Restriction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem centric_inner_restrictions_inner (U V T : {group S})
    (sUV : U \subset V) (cU : DPFusionSystem.centric F U)
    (f g : DPFusionSystem.arrow F V T) :
  (exists t, t \in T /\ {in U, forall u, arrow_value g u = (arrow_value f u) ^ t}) ->
  target_inner f g.
Proof.
have main : forall n (U V T : {group S}) (sUV : U \subset V),
    (#|S| - #|U|)%N = n -> DPFusionSystem.centric F U ->
    forall f g : DPFusionSystem.arrow F V T,
    (exists t, t \in T /\ {in U, forall u, arrow_value g u = (arrow_value f u) ^ t}) ->
    target_inner f g.
  move=> n; elim/ltn_ind: n=> n ih U0 V0 T0 sU0V0 hn cU0 f0 g0 hsame.
  case: (boolP (U0 == V0))=> [/eqP eUV | neUV].
  - subst U0; have [t [Tt ht]] := hsame.
    apply/exists_inP; exists t=> //; apply/forall_inP=> x Vx; apply/eqP; exact: ht x Vx.
  have properUV : U0 \proper V0.
    rewrite properEneq sU0V0 andbT; apply/negP=> /eqP e.
    have eUV : U0 = V0 := val_inj e; by move: neUV; rewrite eUV eqxx.
  pose N := 'N_V0(U0)%G.
  have properUN : U0 \proper N := nilpotent_proper_norm (pgroup_nil (pgroupS (subsetT V0) pS)) properUV.
  have sUN : U0 \subset N := proper_sub properUN.
  have sNV : N \subset V0 := subsetIl _ _.
  have nUN : U0 <| N by rewrite normal_subnorm.
  pose fn : DPFusionSystem.arrow F N T0 := Sub (DPFusion.restrict (val f0) sNV)
    (DPFusionSystem.restriction_allowed sNV (valP f0)).
  pose gn : DPFusionSystem.arrow F N T0 := Sub (DPFusion.restrict (val g0) sNV)
    (DPFusionSystem.restriction_allowed sNV (valP g0)).
  have innerN : target_inner fn gn.
    apply: (DPFusionCentricRigidity.normal_inner_restrictions_inner pS sat nUN cU0).
    have [t [Tt ht]] := hsame; exists t; split=> // u Uu.
    have Nu := subsetP sUN u Uu.
    by rewrite /arrow_value /fn /gn /= !DPFusion.restrict_in //; exact: ht u Uu.
  apply: (ih (#|S| - #|N|)%N _ N V0 T0 sNV erefl
    (DPFusionCentricBasics.centric_overgroup sUN cU0) f0 g0).
  - by rewrite -hn ltn_sub2lE ?max_card //; exact: proper_card properUN.
  - have /exists_inP[t Tt /forall_inP ht] := innerN.
    exists t; split=> // u Nu.
    have h := eqP (ht u Nu).
    by rewrite /arrow_value /fn /gn /= !DPFusion.restrict_in in h.
exact: main _ U V T sUV erefl cU f g.
Qed.

Definition orbit_inclusion (U V : {group S}) (sUV : U \subset V) : orbit_hom F U V :=
  orbit_class (Sub (DPFusion.inclusion sUV) (DPFusionSystem.inclusion_allowed F sUV)).

Definition orbit_restrict (U V T : {group S}) (sUV : U \subset V)
    (f : orbit_hom F V T) : orbit_hom F U T := orbit_compose (orbit_inclusion sUV) f.

Lemma orbit_restrict_injective (U V T : {group S}) (sUV : U \subset V) :
  DPFusionSystem.centric F U -> injective (@orbit_restrict U V T sUV).
Proof.
move=> cU; apply: quotW=> f; apply: quotW=> g.
rewrite /orbit_restrict /orbit_inclusion !orbit_compose_class.
move/orbit_class_eq/exists_inP=> [t Tt /forall_inP ht].
apply/orbit_class_eq; apply: (@centric_inner_restrictions_inner U V T sUV cU f g).
exists t; split=> // u Uu.
have h := eqP (ht u Uu).
by rewrite /arrow_value /DPFusionSystem.arrow_compose /= !DPFusion.compose_in //
  !DPFusion.inclusion_in in h.
Qed.

End Restriction.
End DPFusionCentricRestriction.
