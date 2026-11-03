From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy
  FusionSaturationImage FusionAutomorphisms FusionAlperinWords FusionAlperinWordOperations
  FusionAlperinInductionTools FusionAlperinGrowth FusionAlperinNormalization.
Import DPFusion DPFusionConjugacy DPFusionAlperinWords DPFusionAlperinWordOperations
  DPFusionAlperinInductionTools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAlperinTheorem.
Section Factorization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem strongly_factorizable_iso (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusion.image f = Q -> strongly_factorizable F f.
Proof.
have main : forall n (P Q : {group S}) (f : DPFusion.map P Q),
    (#|S| - #|P|)%N = n -> DPFusionSystem.allowed F f ->
    DPFusion.image f = Q -> strongly_factorizable F f.
  move=> n; elim/ltn_ind: n=> n ih P0 Q0 f0 hn hf of0.
  have hPQ : #|P0| = #|Q0| by rewrite -of0 map_image_card.
  case: (boolP (P0 == [set: S]%G))=> [/eqP eP|neP].
  - have eQ : Q0 = [set: S]%G by apply: subgroup_card_top; rewrite -hPQ eP cardsT.
    subst P0; subst Q0.
    exact: strongly_factorizable_centric (centric_top F) hf.
  have hproper : P0 \proper [set: S].
    rewrite properEcard subsetT /= cardsT.
    rewrite ltn_neqAle (max_card P0) andbT.
    apply/negP=> /eqP hc; have eP := subgroup_card_top hc.
    by move: neP; rewrite eP eqxx.
  have hbig : forall (A B : {group S}) (d : DPFusion.map A B),
      DPFusionSystem.allowed F d -> DPFusion.image d = B ->
      (#|P0| < #|A|)%N -> strongly_factorizable F d.
    move=> A B d hd od hlarge.
    apply: (ih (#|S| - #|A|)%N _ A B d erefl hd od).
    by rewrite -hn ltn_sub2lE ?max_card.
  have [R [/existsP[d /andP[hd /eqP od]] hR]] :=
    fully_normalized_conjugate_exists F P0.
  have hPR : #|P0| = #|R| by rewrite -od map_image_card.
  have [psi [hpsi [opsi [gpsi _]]]] :=
    DPFusionAlperinNormalization.normalizing_words pS sat hproper hbig (erefl #|P0|) hd od hR.
  pose di := DPFusion.compose (onto_inverse of0) d.
  have hdi : DPFusionSystem.allowed F di :=
    DPFusionSystem.composition_closed (onto_inverse_allowed of0 hf) hd.
  have odi : DPFusion.image di = R := compose_onto (onto_inverse_image of0) od.
  have [chi [hchi [ochi [_ gchii]]]] :=
    DPFusionAlperinNormalization.normalizing_words pS sat hproper hbig (esym hPQ) hdi odi hR.
  pose a := DPFusion.compose (onto_inverse opsi) (DPFusion.compose f0 chi).
  have ha : DPFusionSystem.allowed F a :=
    DPFusionSystem.composition_closed (onto_inverse_allowed opsi hpsi)
      (DPFusionSystem.composition_closed hf hchi).
  have ga : strongly_factorizable F a.
    case: (boolP (DPFusionSystem.centric F R))=> [hc|hnc].
    - exact: strongly_factorizable_centric hc ha.
    - have hFC := (DPFusionSaturation.saturation_fully_normalized sat hR).1.
      have [N [h [hRN [hh hext]]]] :=
        DPFusionAlperinGrowth.noncentric_automorphism_extension sat ha hFC hnc.
      have hlarge : (#|P0| < #|N|)%N by rewrite hPR; exact: proper_card hRN.
      have gh : strongly_factorizable F (DPFusion.to_image h) :=
        hbig _ _ _ (DPFusionSystem.image_closed hh)
          (DPFusionSaturationImage.image_to_image h) hlarge.
      exact: strongly_factorizable_of_extension (proper_sub hRN)
        (DPFusionAutomorphisms.endomorphism_image a) hext gh.
  have gcomp := strongly_factorizable_compose
    (strongly_factorizable_compose gpsi ga) gchii.
  have ef : DPFusion.compose (DPFusion.compose psi a) (onto_inverse ochi) = f0.
    apply: DPFusion.map_ext=> x Px.
    have Rx := DPFusion.map_into psi Px.
    have Qx := DPFusion.map_into f0 Px.
    rewrite DPFusion.compose_in // DPFusion.compose_in // /a DPFusion.compose_in //.
    rewrite onto_inverse_cancel // DPFusion.compose_in // onto_inverse_cancel //.
  by rewrite ef in gcomp.
exact: main _ P Q f erefl.
Qed.

(** A literal finite list of actual centric automorphisms and a path whose
    evaluation is the original map, before passage to any orbit quotient. *)
Theorem centric_factorization_iso (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusion.image f = Q ->
  exists l, exists w : @word S F P Q l, evaluation w = f.
Proof.
move=> hf onto; exact: strongly_factorizable_self onto (strongly_factorizable_iso hf onto).
Qed.

(** General maps factor through their actual image, then the standard inclusion. *)
Theorem centric_factorization_hom (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f ->
  exists l, exists w : @word S F P (DPFusion.image f) l,
    DPFusion.compose (evaluation w) (DPFusion.inclusion (DPFusion.image_sub f)) = f.
Proof.
move=> hf.
have [l [w ew]] := centric_factorization_iso (DPFusionSystem.image_closed hf)
  (DPFusionSaturationImage.image_to_image f).
exists l, w; rewrite ew; exact: DPFusion.image_factorization.
Qed.

End Factorization.
End DPFusionAlperinTheorem.


