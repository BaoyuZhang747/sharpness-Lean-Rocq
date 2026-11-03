(** Saturation supplies a linking extension of a prescribed linking
    automorphism whenever its actual normalizer action has the stated range. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionSaturation FusionCentricNormalizerExtension.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemAutomorphisms NormalizerChainTransporter
  LinkingSystemNormalizerSquares LinkingSystemNormalizerExtensionLift.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingAutomorphisms
  DPNormalizerChainTransporter DPLinkingNormalizerSquares DPLinkingNormalizerExtensionLift.
Local Open Scope group_scope.

Module DPLinkingNormalizerExtension.
Section Extension.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).
Variables U N T : Obj.
Hypothesis hUN : val U \subset val N.
Hypothesis hUT : val U \subset val T.
Hypothesis hNN : val N \subset 'N(val U).
Hypothesis hTN : val T \subset 'N(val U).
Variable a : automorphism_group L U.

Definition source_action (x : [subg (val N)]) : automorphism_group L U :=
  normalizer_map L (Sub (val x) (subsetP hNN _ (valP x))).
Definition target_action (y : [subg (val T)]) : automorphism_group L U :=
  normalizer_map L (Sub (val y) (subsetP hTN _ (valP y))).

Hypothesis action_range : forall x : [subg (val N)],
  exists y : [subg (val T)], target_action y = source_action x ^ a.

Lemma action_intertwines (x : [subg (val N)]) (y : [subg (val T)])
    (hy : target_action y = source_action x ^ a) :
    source_action x * a = a * target_action y.
Proof. by rewrite hy /conjg !mulgA mulgV mul1g. Qed.

Lemma projected_action (x : [subg (val N)]) (y : [subg (val T)])
    (hy : target_action y = source_action x ^ a) u (hu : u \in val U) :
    DPFusion.map_fun (val (linking_projection L a)) (u ^ val x) =
      DPFusion.map_fun (val (linking_projection L a)) u ^ val y.
Proof.
have he := congr1 (fun t : automorphism_group L U =>
  DPFusion.map_fun (val (linking_projection L t)) u) (action_intertwines hy).
change (DPFusion.map_fun (val (linking_projection L (linking_compose L (source_action x) a))) u =
  DPFusion.map_fun (val (linking_projection L (linking_compose L a (target_action y)))) u) in he.
rewrite !projection_compose in he.
change (DPFusion.map_fun (DPFusion.compose (val (linking_projection L (source_action x)))
    (val (linking_projection L a))) u =
  DPFusion.map_fun (DPFusion.compose (val (linking_projection L a))
    (val (linking_projection L (target_action y)))) u) in he.
by rewrite !DPFusion.compose_in // /source_action /target_action
  !normalizer_projection ?DPFusion.map_into // in he.
Qed.

Definition fusion_top : DPFusion.map (val U) (val T) :=
  DPFusion.compose (val (linking_projection L a)) (DPFusion.inclusion hUT).

Lemma fusion_top_in u (hu : u \in val U) :
  DPFusion.map_fun fusion_top u = DPFusion.map_fun (val (linking_projection L a)) u.
Proof. by rewrite /fusion_top DPFusion.compose_in // DPFusion.inclusion_in ?DPFusion.map_into. Qed.

Lemma fusion_top_allowed : DPFusionSystem.allowed F fusion_top.
Proof.
apply: DPFusionSystem.composition_closed (valP (linking_projection L a)) _.
exact: DPFusionSystem.inclusion_allowed.
Qed.

Lemma fusion_action_compatible n (hn : n \in val N) :
  exists t, t \in val T /\ forall u, u \in val U ->
    DPFusion.map_fun fusion_top (u ^ n) = DPFusion.map_fun fusion_top u ^ t.
Proof.
have [y hy] := action_range (Sub n hn).
exists (val y); split; first exact: valP.
move=> u hu.
have hun : u ^ n \in val U by rewrite memJ_norm // (subsetP hNN _ hn).
rewrite !fusion_top_in //.
exact (@projected_action (Sub n hn) y hy u hu).
Qed.

Theorem exists_linking_normalizer_extension p (sat : DPFusionSaturation.saturated F p) :
  exists b : linking_hom L N T,
    linking_compose L a (inclusion L hUT) = linking_compose L (inclusion L hUN) b.
Proof.
have [r [hr he]] := @DPFusionCentricNormalizerExtension.centric_normalizer_extension
  S F p sat (val U) (val N) (val T) fusion_top fusion_top_allowed (valP U)
  hUN hNN fusion_action_compatible.
apply: (@exists_prescribed_extension S F L U N T hUN hUT a (Sub r hr)).
move=> u hu; rewrite (he u hu); exact: fusion_top_in.
Qed.
End Extension.

Section Matching.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).
Variables U N T : Obj.
Hypothesis hUN : val U \subset val N.
Hypothesis hUT : val U \subset val T.
Hypothesis hNN : val N \subset 'N(val U).
Hypothesis hTN : val T \subset 'N(val U).
Variable a : automorphism_group L U.
Variable b : linking_hom L N T.
Hypothesis square : linking_compose L a (inclusion L hUT) =
  linking_compose L (inclusion L hUN) b.

Theorem extension_matches_action (x : [subg (val N)]) (y : [subg (val T)])
    (hy : @target_action S F L U T hTN y = @source_action S F L U N hNN x ^ a) :
  DPFusion.map_fun (val (linking_projection L b)) (val x) = val y.
Proof.
have he := @extension_conjugation S F L U N T hUN hUT hNN hTN a b square x.
have hm : normalizer_map L (@target_normalizer S F L U N T hTN b x) =
  normalizer_map L (Sub (val y) (subsetP hTN _ (valP y))).
  exact (eq_trans he (esym hy)).
have hv := congr1 (fun z : [subg 'N(val U)] => val z) (normalizer_map_injective hm).
exact hv.
Qed.
End Matching.
End DPLinkingNormalizerExtension.

Check DPLinkingNormalizerExtension.exists_linking_normalizer_extension.
Check DPLinkingNormalizerExtension.extension_matches_action.
Print Assumptions DPLinkingNormalizerExtension.exists_linking_normalizer_extension.
Print Assumptions DPLinkingNormalizerExtension.extension_matches_action.
