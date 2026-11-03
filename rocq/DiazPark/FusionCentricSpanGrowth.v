From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans CategoryFiniteSpanGrowth
  CategoryFiniteSpanTransport FusionMaps FusionSystems FusionOrbit FusionFiniteCategory FusionSaturation
  FusionCentricSpanNormalization FusionCentricNormalizedSpans FusionCentricNormalizedFactors
  FusionCentricNormalizedGrowth FusionCentricInclusionSpans BurnsideFusionRanks.
Import DPFusionOrbit DPFusionCentricNormalizedSpans DPFusionCentricNormalizedFactors
  DPFusionCentricInclusionSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricSpanGrowth.
Section Growth.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Local Notation rank := (DPBurnsideFusionRanks.centric_rank (F:=F)).
Variables P Q : fc_object C.

Theorem centric_span_growth : @span_growth_diamond C P Q rank.
Proof.
move=> X A B hA hB f g hf hg.
pose x := repr (span_first X).
pose a0 := repr (span_first A).
pose b0 := repr (span_first B).
have hx : orbit_class x = span_first X := reprK _.
have hfa : orbit_class (DPFusionSystem.arrow_compose (repr (val f)) a0) = orbit_class x.
  rewrite /a0 /x -orbit_compose_class /orbit_class !reprK; exact: span_factor_first f.
have hgb : orbit_class (DPFusionSystem.arrow_compose (repr (val g)) b0) = orbit_class x.
  rewrite /b0 /x -orbit_compose_class /orbit_class !reprK; exact: span_factor_first g.
have [a [hra hrawa]] := DPFusionCentricSpanNormalization.adjust_raw_factor hfa.
have [b [hrb hrawb]] := DPFusionCentricSpanNormalization.adjust_raw_factor hgb.
have ha : orbit_class a = span_first A.
  have ea : orbit_class a0 = orbit_class a by apply/orbit_class_eq.
  by rewrite -ea /a0 /orbit_class reprK.
have hb : orbit_class b = span_first B.
  have eb : orbit_class b0 = orbit_class b by apply/orbit_class_eq.
  by rewrite -eb /b0 /orbit_class reprK.
pose nx := @normalized_span S F P Q X x.
pose na := @normalized_span S F P Q A a.
pose nb := @normalized_span S F P Q B b.
pose ex := @normalized_span_iso S F P Q X x hx.
pose ea := @normalized_span_iso S F P Q A a ha.
pose eb := @normalized_span_iso S F P Q B b hb.
pose fn := @normalized_factor S F P Q X A f x a hx ha hrawa.
pose gn := @normalized_factor S F P Q X B g x b hx hb hrawb.
have trf := @normalized_factor_triangle S F P Q X A f x a hx ha hrawa.
have trg := @normalized_factor_triangle S F P Q X B g x b hx hb hrawb.
have rankx := @span_isomorphism_rank C P Q rank (@DPBurnsideFusionRanks.centric_rank_le S F) X nx ex.
have ranka := @span_isomorphism_rank C P Q rank (@DPBurnsideFusionRanks.centric_rank_le S F) A na ea.
have rankb := @span_isomorphism_rank C P Q rank (@DPBurnsideFusionRanks.centric_rank_le S F) B nb eb.
have largea : (rank (span_object nx) < rank (span_object na))%N by rewrite -rankx -ranka.
have largeb : (rank (span_object nx) < rank (span_object nb))%N by rewrite -rankx -rankb.
pose sRA := @image_sub_image S F P Q X A f x a hrawa.
pose sRB := @image_sub_image S F P Q X B g x b hrawb.
have agreea := span_factor_second fn.
have agreeb := span_factor_second gn.
have [Y [Z [W [u [v [s [t [aa [bb [hY [hZ [hu [hs hab]]]]]]]]]]]]] :=
  @DPFusionCentricNormalizedGrowth.normalized_growth_diamond S F p pS sat P Q
    (span_object nx) (span_object na) (span_object nb)
    (DPFusion.image_sub (val x)) (DPFusion.image_sub (val a)) (DPFusion.image_sub (val b))
    sRA sRB (span_second nx) (span_second na) (span_second nb) agreea agreeb largea largeb.
have hu' : span_factor_compose u v = fn.
  apply: val_inj; have H := congr1 val hu; exact H.
have hs' : span_factor_compose s t = gn.
  apply: val_inj; have H := congr1 val hs; exact H.
have [u0 [v0 [s0 [t0 H]]]] := @span_diamond_transport C P Q rank
  (@DPBurnsideFusionRanks.centric_rank_le S F) X A B nx na nb ex ea eb f g fn gn
  trf trg Y Z W u v s t aa bb hY hZ hu' hs' hab.
exists Y,Z,W,u0,v0,s0,t0,aa,bb; exact H.
Qed.

End Growth.
End DPFusionCentricSpanGrowth.
