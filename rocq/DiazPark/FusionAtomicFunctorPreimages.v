From mathcomp Require Import all_ssreflect all_fingroup quotient pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionOrbit
  FusionOuterAutomorphisms FusionOuterOrbit FusionOuterAction FusionCentricCriterion FusionCentricBasics.
Import DPFusion DPFusionOrbit DPFusionOuter DPFusionOuterOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAtomicPreimages.
Section Preimages.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Q : {group S}.
Hypothesis centricQ : DPFusionSystem.centric F Q.
Local Notation A := (DPFusionSaturation.aut_group F Q).
Local Notation G0 := (outer_group F Q).
Definition outer_type := [subg G0]%type.
Definition ambient_outer : {group outer_type} := (subg G0 @* ambient_outer_group Q)%G.

Lemma conjugation_allowed n : n \in 'N(Q) -> conj_aut Q n \in A.
Proof.
move=> Nn; apply: (subsetP (DPFusionSaturation.ambient_aut_sub F Q)).
by apply/morphimP; exists n.
Qed.
Lemma conjugation_outer_mem n : n \in 'N(Q) -> coset (inner Q) (conj_aut Q n) \in G0.
Proof. move=> Nn; exact: mem_quotient _ (conjugation_allowed Nn). Qed.

Definition theta n : outer_type := subg G0 (coset (inner Q) (conj_aut Q n)).
Lemma theta_value n : n \in 'N(Q) -> val (theta n) = coset (inner Q) (conj_aut Q n).
Proof. move=> Nn; exact: subgK (conjugation_outer_mem Nn). Qed.
Lemma theta_morphic : {in 'N(Q) &, {morph theta : n m / n*m}}.
Proof.
move=> n m Nn Nm; apply: val_inj.
rewrite theta_value ?groupM //= !theta_value // conj_aut_morphM //.
exact: (morphM (coset (inner Q))
  (subsetP (normal_norm (inner_normal F Q)) _ (conjugation_allowed Nn))
  (subsetP (normal_norm (inner_normal F Q)) _ (conjugation_allowed Nm))).
Qed.
Canonical theta_morphism := Morphism theta_morphic.

Lemma theta_image : theta @* 'N(Q) = ambient_outer.
Proof.
apply/setP=> h; apply/morphimP/morphimP.
- move=> [n Nn _ ->].
  exists (coset (inner Q) (conj_aut Q n)); first exact: conjugation_outer_mem Nn.
  - apply/morphimP; exists (conj_aut Q n).
    + exact: subsetP (normal_norm (inner_normal F Q)) _ (conjugation_allowed Nn).
    + by apply/morphimP; exists n.
    + by [].
  - by [].
- move=> [g Gg /morphimP[a Na /morphimP[n Nn _ ea] eg] eh].
  exists n=> //; by rewrite eh /theta eg ea.
Qed.

Lemma theta_kernel : 'ker theta_morphism = Q.
Proof.
apply/setP=> n; apply/morphpreP/idP.
- move=> [Nn /set1P e].
  have ec := congr1 val e; rewrite theta_value // in ec.
  have Ia : conj_aut Q n \in inner Q.
    apply: coset_idr _ ec.
    exact: subsetP (normal_norm (inner_normal F Q)) _ (conjugation_allowed Nn).
  have /morphimP[q _ Qq ea] := Ia.
  have Cn : n*q^-1 \in 'C(Q).
    apply/centP=> x Qx; apply/esym/commgP/conjg_fixP.
    rewrite conjgM -(@norm_conj_autE S Q n x Nn Qx) ea conj_autE // conjgK.
    by [].
  have h := groupM (subsetP (DPFusionCentricCriterion.centric_self_centralizing centricQ) _ Cn) Qq.
  by rewrite mulgKV in h.
- move=> Qn; split; first exact: subsetP (normG Q) n Qn.
  apply/set1P; apply: val_inj; rewrite theta_value ?(subsetP (normG Q) _ Qn) //.
  apply: coset_id; exact: mem_morphim (subsetP (normG Q) n Qn) Qn.
Qed.

Definition preimage (H : {group outer_type}) : {group S} := (theta @*^-1 H)%G.
Lemma preimage_sub_normalizer H : preimage H \subset 'N(Q).
Proof. exact: morphpre_sub. Qed.
Lemma source_sub_preimage H : Q \subset preimage H.
Proof. rewrite -theta_kernel; exact: ker_sub_pre. Qed.
Lemma source_normal_preimage H : Q <| preimage H.
Proof. rewrite -theta_kernel; exact: ker_normal_pre. Qed.
Lemma preimage_centric H : DPFusionSystem.centric F (preimage H).
Proof. exact: DPFusionCentricBasics.centric_overgroup (source_sub_preimage H) centricQ. Qed.
Lemma preimage_one : preimage 1%G = Q.
Proof. apply: val_inj; exact: theta_kernel. Qed.
Lemma preimage_image (H : {group outer_type}) : H \subset ambient_outer -> theta @* preimage H = H.
Proof. move=> hH; apply: morphpreK; by rewrite theta_image. Qed.
Lemma preimage_card (H : {group outer_type}) : H \subset ambient_outer ->
  #|preimage H| = (#|Q| * #|H|)%N.
Proof.
move=> hH; change (#|theta @*^-1 H| = (#|Q| * #|H|)%N).
rewrite card_morphpre ?theta_kernel //; by rewrite theta_image.
Qed.

Lemma ambient_outer_sylow_subtype (p : nat) (sat : DPFusionSaturation.saturated F p)
    (normalizedQ : DPFusionSystem.fully_normalized F Q) :
  p.-Sylow([set: outer_type]) ambient_outer.
Proof.
have h := morphim_pSylow (subg G0) (ambient_outer_sub F Q)
  (ambient_outer_sylow sat normalizedQ).
by rewrite im_subg in h.
Qed.

End Preimages.
End DPFusionAtomicPreimages.

