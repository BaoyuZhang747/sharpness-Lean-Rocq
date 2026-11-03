From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category CategoryFinite CategoryFiniteProducts CategoryFiniteSpans
  CategoryFiniteSpanProducts CategoryFiniteSpanGrowth FusionMaps FusionSystems FusionFiniteCategory
  FusionSaturation BurnsideFusionRanks FusionCentricSpanGrowth FusionCentricSpanRigidity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentricProducts.
Section Products.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Local Notation rank := (DPBurnsideFusionRanks.centric_rank (F:=F)).

Lemma equal_rank_isomorphism (A B : fc_object C) (f : fc_hom C A B)
    (h : rank A = rank B) : exists e : @isomorphism (fc_category C) A B, iso_hom e = f.
Proof.
exists (DPBurnsideFusionRanks.centric_equal_rank_iso f h).
exact: DPBurnsideFusionRanks.centric_equal_rank_iso_hom.
Qed.

Theorem centric_maximal_span_alignment (P Q : fc_object C)
    (X A B : finite_span C P Q) : span_maximal rank A -> span_maximal rank B ->
    forall (f : span_factor X A) (g : span_factor X B),
    exists k : span_factor A B, span_factor_compose f k = g.
Proof.
exact (@span_maximal_alignment_of_growth C P Q rank
  (@DPBurnsideFusionRanks.centric_rank_le S F) equal_rank_isomorphism
  (@DPFusionCentricSpanGrowth.centric_span_growth S F p pS sat P Q) X A B).
Qed.

Definition centric_product (P Q : fc_object C) :
    @finite_product_decomposition (fc_category C) P Q :=
  @finite_product_of_maximal_spans C P Q rank
    (@DPBurnsideFusionRanks.centric_rank_le S F) equal_rank_isomorphism
    (@centric_maximal_span_alignment P Q)
    (@DPFusionCentricSpanRigidity.centric_span_maximal_rigid S F p sat P Q).

Theorem centric_product_encode_injective (P Q X : fc_object C) :
    injective (@fp_encode (fc_category C) P Q X (centric_product P Q)).
Proof. exact: fp_encode_injective. Qed.

Theorem centric_product_encode_surjective (P Q X : fc_object C)
    (a : (fc_hom C X P * fc_hom C X Q)%type) :
    exists t : fp_factors (centric_product P Q) X,
      fp_encode (centric_product P Q) t = a.
Proof. exact: fp_encode_surjective. Qed.

Theorem centric_product_encode_natural (P Q X Y : fc_object C)
    (h : fc_hom C Y X) (t : fp_factors (centric_product P Q) X) :
    fp_encode (centric_product P Q) (fp_precompose (centric_product P Q) h t) =
      (fc_compose h (fst (fp_encode (centric_product P Q) t)),
       fc_compose h (snd (fp_encode (centric_product P Q) t))).
Proof. exact: fp_encode_precompose. Qed.
End Products.
End DPFusionCentricProducts.
