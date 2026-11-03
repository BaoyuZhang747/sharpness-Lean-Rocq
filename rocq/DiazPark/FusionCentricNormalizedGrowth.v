From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup sylow nilpotent.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans FusionMaps FusionSystems
  FusionOrbit FusionFiniteCategory FusionSaturation FusionCentricBasics FusionCentricRestriction
  FusionCentricInclusionSpans FusionCentricOrbitAmalgamation BurnsideFusionRanks.
Import DPFusionOrbit DPFusionCentricInclusionSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricNormalizedGrowth.
Section Growth.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation inc := (DPFusionCentricRestriction.orbit_inclusion F).

Lemma orbit_restrict_twice (U V T Q : {group S})
    (sUV : U \subset V) (sVT : V \subset T) (sUT : U \subset T) (f : orbit_hom F T Q) :
  orbit_compose (inc sUV) (orbit_compose (inc sVT) f) = orbit_compose (inc sUT) f.
Proof.
have H := @Category.compose_assoc (orbit_category F) U V T Q (inc sUV) (inc sVT) f.
change (orbit_compose (orbit_compose (inc sUV) (inc sVT)) f =
  orbit_compose (inc sUV) (orbit_compose (inc sVT) f)) in H.
rewrite -H.
by rewrite (orbit_inclusion_trans F sUV sVT sUT).
Qed.

Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Local Notation rank := (DPBurnsideFusionRanks.centric_rank (F:=F)).
Variables P Q R A B : fc_object C.
Hypotheses (sRP : val R \subset val P) (sAP : val A \subset val P) (sBP : val B \subset val P).
Hypotheses (sRA : val R \subset val A) (sRB : val R \subset val B).
Variables (gamma : fc_hom C R Q) (alpha : fc_hom C A Q) (beta : fc_hom C B Q).
Hypotheses (ha : orbit_compose (inc sRA) alpha = gamma) (hb : orbit_compose (inc sRB) beta = gamma).
Hypotheses (hRA : (#|val R| < #|val A|)%N) (hRB : (#|val R| < #|val B|)%N).
Local Notation X := (inclusion_span sRP gamma).
Local Notation AA := (inclusion_span sAP alpha).
Local Notation BB := (inclusion_span sBP beta).
Local Notation f := (@inclusion_span_factor S F P Q R A sRP sAP gamma alpha sRA ha).
Local Notation g := (@inclusion_span_factor S F P Q R B sRP sBP gamma beta sRB hb).

Theorem normalized_growth_diamond :
  exists Y Z W : finite_span C P Q,
  exists (u : span_factor X Y) (v : span_factor Y AA)
    (s : span_factor X Z) (t : span_factor Z BB)
    (a : span_factor Y W) (b : span_factor Z W),
    (rank (span_object X) < rank (span_object Y))%N /\
    (rank (span_object X) < rank (span_object Z))%N /\
    span_factor_compose u v = f /\ span_factor_compose s t = g /\
    span_factor_compose u a = span_factor_compose s b.
Proof.
pose N := 'N_(val A)(val R)%G.
pose M := 'N_(val B)(val R)%G.
pose D := (N <*> M)%G.
have prRA : val R \proper val A by rewrite properEcard sRA hRA.
have prRB : val R \proper val B by rewrite properEcard sRB hRB.
have prRN : val R \proper N := nilpotent_proper_norm (pgroup_nil (pgroupS (subsetT (val A)) pS)) prRA.
have prRM : val R \proper M := nilpotent_proper_norm (pgroup_nil (pgroupS (subsetT (val B)) pS)) prRB.
have sRN := proper_sub prRN.
have sRM := proper_sub prRM.
have sNA : N \subset val A := subsetIl _ _.
have sMB : M \subset val B := subsetIl _ _.
have sNP := subset_trans sNA sAP.
have sMP := subset_trans sMB sBP.
have sND : N \subset D := joing_subl _ _.
have sMD : M \subset D := joing_subr _ _.
have sRD := subset_trans sRN sND.
have sDP : D \subset val P by rewrite join_subG sNP sMP.
pose nobj : fc_object C := Sub N (DPFusionCentricBasics.centric_overgroup sRN (valP R)).
pose mobj : fc_object C := Sub M (DPFusionCentricBasics.centric_overgroup sRM (valP R)).
pose dobj : fc_object C := Sub D (DPFusionCentricBasics.centric_overgroup sRD (valP R)).
have [delta hd] := @DPFusionCentricOrbitAmalgamation.orbit_normalizer_amalgamation
  S F p sat (val R) (val A) (val B) (val Q) sRA sRB (valP R) gamma alpha beta ha hb.
have hd' : orbit_compose (inc sRD) delta = gamma.
  have e : inc sRD = inc (@DPFusionCentricOrbitAmalgamation.source_sub_domain S (val R) (val A) (val B) sRA).
    have ep : sRD = (@DPFusionCentricOrbitAmalgamation.source_sub_domain S (val R) (val A) (val B) sRA) := bool_irrelevance _ _.
    by rewrite ep.
  by rewrite e.
pose ny : fc_hom C nobj Q := orbit_compose (inc sNA) alpha.
pose mz : fc_hom C mobj Q := orbit_compose (inc sMB) beta.
pose Y := @inclusion_span S F P Q nobj sNP ny.
pose Z := @inclusion_span S F P Q mobj sMP mz.
pose W := @inclusion_span S F P Q dobj sDP delta.
have huy : orbit_compose (inc sRN) ny = gamma by rewrite /ny (orbit_restrict_twice sRN sNA sRA) ha.
have hsz : orbit_compose (inc sRM) mz = gamma by rewrite /mz (orbit_restrict_twice sRM sMB sRB) hb.
have hyw : orbit_compose (inc sND) delta = ny.
  apply: (@DPFusionCentricRestriction.orbit_restrict_injective S F p pS sat (val R) N (val Q) sRN (valP R)).
  change (orbit_compose (inc sRN) (orbit_compose (inc sND) delta) = orbit_compose (inc sRN) ny).
  by rewrite (orbit_restrict_twice sRN sND sRD) hd' huy.
have hzw : orbit_compose (inc sMD) delta = mz.
  apply: (@DPFusionCentricRestriction.orbit_restrict_injective S F p pS sat (val R) M (val Q) sRM (valP R)).
  change (orbit_compose (inc sRM) (orbit_compose (inc sMD) delta) = orbit_compose (inc sRM) mz).
  by rewrite (orbit_restrict_twice sRM sMD sRD) hd' hsz.
pose u := @inclusion_span_factor S F P Q R nobj sRP sNP gamma ny sRN huy.
pose v := @inclusion_span_factor S F P Q nobj A sNP sAP ny alpha sNA erefl.
pose s := @inclusion_span_factor S F P Q R mobj sRP sMP gamma mz sRM hsz.
pose t := @inclusion_span_factor S F P Q mobj B sMP sBP mz beta sMB erefl.
pose a := @inclusion_span_factor S F P Q nobj dobj sNP sDP ny delta sND hyw.
pose b := @inclusion_span_factor S F P Q mobj dobj sMP sDP mz delta sMD hzw.
exists Y,Z,W,u,v,s,t,a,b; split; first exact: proper_card prRN.
split; first exact: proper_card prRM.
split; first by apply: val_inj; exact: (orbit_inclusion_trans F).
split; first by apply: val_inj; exact: (orbit_inclusion_trans F).
apply: val_inj; change (orbit_compose (inc sRN) (inc sND) = orbit_compose (inc sRM) (inc sMD)).
by rewrite (orbit_inclusion_trans F sRN sND sRD) (orbit_inclusion_trans F sRM sMD sRD).
Qed.

End Growth.
End DPFusionCentricNormalizedGrowth.
