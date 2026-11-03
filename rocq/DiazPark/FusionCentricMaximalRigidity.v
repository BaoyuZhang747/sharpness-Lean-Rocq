From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category CategoryFinite CategoryFiniteSpans CategoryFiniteSpanProducts
  FusionMaps FusionSystems FusionOrbit FusionFiniteCategory FusionSaturation FusionCentricBasics
  FusionCentricNormalizerExtension FusionCentricAmalgamation FusionCentricInclusionSpans
  FusionCentricRestriction BurnsideFusionRanks.
Import DPFusionOrbit DPFusionCentricInclusionSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricMaximalRigidity.
Section Normalized.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Local Notation rank := (DPBurnsideFusionRanks.centric_rank (F:=F)).
Variables P Q A : fc_object C.
Variable sAP : val A \subset val P.
Variable alpha : fc_hom C A Q.
Local Notation X := (@inclusion_span S F P Q A sAP alpha).
Hypothesis maximalX : span_maximal rank X.

Theorem normalized_maximal_rigid (f : span_factor X X) : val f = fc_identity A.
Proof.
pose sigma := repr (val f).
pose incraw : DPFusionSystem.arrow F (val A) (val P) :=
  Sub (DPFusion.inclusion sAP) (DPFusionSystem.inclusion_allowed F sAP).
have hfirst : orbit_class incraw = orbit_class (DPFusionSystem.arrow_compose sigma incraw).
  rewrite -orbit_compose_class /sigma /orbit_class reprK.
  exact: esym (span_factor_first f).
have /orbit_class_eq/exists_inP[n Pn /forall_inP hn] := hfirst.
have sigma_conj : {in val A, forall x, DPFusion.map_fun (val sigma) x = x ^ n}.
  move=> x Ax; have H := eqP (hn x Ax).
  by rewrite /arrow_value /DPFusionSystem.arrow_compose /incraw /= DPFusion.compose_in //
    !DPFusion.inclusion_in ?DPFusion.map_into in H.
have Nn : n \in 'N(val A).
  rewrite inE; apply/subsetP=> y /imsetP[x Ax ->].
  rewrite -(sigma_conj x Ax); exact: DPFusion.map_into Ax.
pose ar := repr alpha.
have hsecond : orbit_class ar = orbit_class (DPFusionSystem.arrow_compose sigma ar).
  rewrite -orbit_compose_class /sigma /ar /orbit_class !reprK.
  exact: esym (span_factor_second f).
have /orbit_class_eq/exists_inP[q Qq /forall_inP hq] := hsecond.
have compatn : n \in DPFusionCentricAmalgamation.compatible_group (val ar).
  apply/setIdP; split=> //; apply/exists_inP; exists q=> //; apply/forall_inP=> x Ax.
  have H := hq x Ax.
  rewrite /arrow_value /DPFusionSystem.arrow_compose /= DPFusion.compose_in // sigma_conj // in H.
pose H := (val A <*> <[n]>)%G.
have sAH : val A \subset H := joing_subl _ _.
have nH : n \in H := subsetP (joing_subr (val A) <[n]>) n (cycle_id n).
have sHP : H \subset val P by rewrite join_subG sAP cycle_subG Pn.
have sHC : H \subset DPFusionCentricAmalgamation.compatible_group (val ar).
  by rewrite join_subG DPFusionCentricAmalgamation.compatible_group_contains_source cycle_subG compatn.
have sHN := subset_trans sHC (DPFusionCentricAmalgamation.compatible_group_normalizes (val ar)).
have [delta [hd hext]] := @DPFusionCentricNormalizerExtension.centric_normalizer_extension
  S F p sat (val A) H (val Q) (val ar) (valP ar) (valP A) sAH sHN
  (fun n0 hn0 => DPFusionCentricAmalgamation.compatible_group_witness (subsetP sHC n0 hn0)).
pose Hobj : fc_object C := Sub H (DPFusionCentricBasics.centric_overgroup sAH (valP A)).
pose dr : DPFusionSystem.arrow F H (val Q) := Sub delta hd.
pose Y := @inclusion_span S F P Q Hobj sHP (orbit_class dr).
have restrict_delta : orbit_compose (DPFusionCentricRestriction.orbit_inclusion F sAH) (orbit_class dr) = alpha.
  rewrite /DPFusionCentricRestriction.orbit_inclusion orbit_compose_class -(reprK alpha).
  apply: congr1; apply: DPFusionSystem.arrow_ext=> x Ax.
  rewrite /DPFusionSystem.arrow_compose /= DPFusion.compose_in // DPFusion.inclusion_in //.
  exact: hext x Ax.
pose extension := @inclusion_span_factor S F P Q A Hobj sAP sHP alpha (orbit_class dr) sAH restrict_delta.
have /span_maximalP hm := maximalX.
have smaller := hm Y extension.
have hHA : val H = val (val A).
  apply/esym/eqP; rewrite eqEcard sAH /=.
  exact smaller.
have An : n \in val A by rewrite -hHA.
rewrite -(reprK (val f)).
change (orbit_class sigma = orbit_class (DPFusionSystem.arrow_identity F (val A))).
apply/orbit_class_eq; apply: target_inner_reverse.
apply/exists_inP; exists n=> //; apply/forall_inP=> x Ax.
by rewrite /arrow_value /DPFusionSystem.arrow_identity /= DPFusion.identity_in // sigma_conj.
Qed.

End Normalized.
End DPFusionCentricMaximalRigidity.
