From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryIsoConjugation CategoryFinite CategoryFiniteSpans CategoryFiniteSpanProducts
  FusionMaps FusionSystems FusionOrbit FusionFiniteCategory FusionSaturation
  FusionCentricNormalizedSpans FusionCentricMaximalRigidity BurnsideFusionRanks.
Import DPFusionOrbit DPFusionCentricNormalizedSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricSpanRigidity.
Section Rigidity.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Local Notation rank := (DPBurnsideFusionRanks.centric_rank (F:=F)).
Variables P Q : fc_object C.
Local Notation SC := (finite_span_category C P Q).

Theorem centric_span_maximal_rigid (A : finite_span C P Q)
    (hA : span_maximal rank A) (f : span_factor A A) : val f = fc_identity (span_object A).
Proof.
pose a := repr (span_first A).
have ha : orbit_class a = span_first A := reprK _.
pose N := @normalized_span S F P Q A a.
pose e := @normalized_span_iso S F P Q A a ha.
have hN : span_maximal rank N := span_maximal_iso
  (@DPBurnsideFusionRanks.centric_rank_le S F) (iso_symm e) hA.
pose fn : span_factor N N := span_factor_compose (span_factor_compose (iso_inv e) f) (iso_hom e).
have hn := @DPFusionCentricMaximalRigidity.normalized_maximal_rigid S F p sat P Q
  (span_object N) (DPFusion.image_sub (val a)) (span_second N) hN fn.
have hn' : fn = @identity (fc_category SC) N.
  apply: val_inj; exact hn.
have hf : f = @identity (fc_category SC) A := iso_conjugate_identity e f hn'.
exact (congr1 val hf).
Qed.

End Rigidity.
End DPFusionCentricSpanRigidity.
