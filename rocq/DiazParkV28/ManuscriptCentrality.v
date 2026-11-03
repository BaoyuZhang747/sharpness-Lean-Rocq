(** Definition 2.2 centrality, and the actual central quotient, with the
    manuscript's normality-plus-extension premise. *)
From mathcomp Require Import all_ssreflect all_fingroup center pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientSaturation.
Import DPFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPV28ManuscriptCentrality.
Section Centrality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition central_extension_property (Z : {group S}) : Prop :=
  forall (P Q : {group S}) (f : DPFusion.map P Q),
    DPFusionSystem.allowed F f ->
    exists fhat : DPFusion.map (P <*> Z)%G (Q <*> Z)%G,
      DPFusionSystem.allowed F fhat /\
      {in P, fhat =1 f} /\ {in Z, fhat =1 id}.

Definition manuscript_central (Z : {group S}) : Prop :=
  (Z <| [set: S]%G) /\ central_extension_property Z.

Lemma normal_join_product (Z : {group S})
    (nZ : Z <| [set: S]%G) (P : {group S}) : P <*> Z = P * Z.
Proof.
apply: norm_joinEl.
exact: subset_trans (subsetT P) (normal_norm nZ).
Qed.

Lemma extension_sub_center (Z : {group S}) :
  central_extension_property Z -> Z \subset 'Z([set: S]).
Proof.
move=> h; apply/subsetP=> z Zz; apply/centerP; split.
- by rewrite inE.
- move=> s _.
  have sZT : Z :^ s \subset [set: S] := subsetT _.
  pose f : DPFusion.map Z [set: S]%G := DPFusion.conjugation sZT.
  have hf : DPFusionSystem.allowed F f :=
    DPFusionSystem.conjugation_closed F sZT.
  have [fhat [_ [hext hfix]]] := h Z [set: S]%G f hf.
  have hz : f z = z := eq_trans (esym (hext z Zz)) (hfix z Zz).
  have hc : z ^ s = z.
    rewrite -(DPFusion.conjugation_in sZT Zz).
    exact: hz.
  apply/commgP/conjg_fixP.
  exact: hc.
Qed.

Definition central_of_manuscript (Z : {group S})
    (hZ : manuscript_central Z) : DPFusionQuotient.central F Z.
Proof.
case: hZ=> nZ ext; constructor.
- exact: extension_sub_center ext.
- exact ext.
Defined.

Lemma manuscript_of_central (Z : {group S}) :
  DPFusionQuotient.central F Z -> manuscript_central Z.
Proof.
move=> cZ; split.
- exact: DPFusionQuotient.central_normal cZ.
- exact: DPFusionQuotient.central_extension cZ.
Qed.

Theorem manuscript_central_iff (Z : {group S}) :
  manuscript_central Z <-> DPFusionQuotient.central F Z.
Proof. split; [exact: central_of_manuscript | exact: manuscript_of_central]. Qed.

Lemma manuscript_central_sub_center (Z : {group S}) :
  manuscript_central Z -> Z \subset 'Z([set: S]).
Proof. move=> hZ; exact: DPFusionQuotient.central_sub_center (central_of_manuscript hZ). Qed.

Lemma manuscript_central_fixes (Z : {group S}) (hZ : manuscript_central Z)
    (P Q : {group S}) (f : DPFusion.map P Q) :
  Z \subset P -> DPFusionSystem.allowed F f -> {in Z, f =1 id}.
Proof.
exact (@DPFusionQuotient.central_fixes S F Z (central_of_manuscript hZ) P Q f).
Qed.

Definition manuscript_quotient_system (Z : {group S})
    (hZ : manuscript_central Z) : DPFusionSystem.system (coset_of Z) :=
  DPFusionQuotientConstruction.system (central_of_manuscript hZ).

Theorem manuscript_quotient_allowed_iff_lift (Z : {group S})
    (hZ : manuscript_central Z) (P Q : {group coset_of Z}) (b : DPFusion.map P Q) :
  DPFusionSystem.allowed (manuscript_quotient_system hZ) b <->
  exists f : DPFusion.map (DPFusionQuotientConstruction.preimage P)
    (DPFusionQuotientConstruction.preimage Q),
    DPFusionSystem.allowed F f /\
    forall x, x \in DPFusionQuotientConstruction.preimage P ->
      b (coset Z x) = coset Z (f x).
Proof. exact: DPFusionQuotientConstruction.allowed_iff_lift. Qed.

Theorem manuscript_central_quotient_saturated (Z : {group S})
    (hZ : manuscript_central Z) (p : nat)
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p) :
  DPFusionSaturation.saturated (manuscript_quotient_system hZ) p.
Proof.
exact: (@DPFusionQuotientSaturation.central_quotient_saturated
  S F Z (central_of_manuscript hZ) p pS sat).
Qed.
End Centrality.
End DPV28ManuscriptCentrality.
