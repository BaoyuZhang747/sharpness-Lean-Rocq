(** Saturation supplies an actual image chain with Sylow K-automizer. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionKNormalization.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainStabilizer
  NormalizerChainTransport NormalizerChainTransportStabilizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainStabilizer DPNormalizerChainTransport
  DPNormalizerChainTransportStabilizer.
Local Open Scope group_scope.

Module DPNormalizerChainSylowAutomizer.
Section Representatives.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variable p : nat.
Hypothesis hS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem exists_sylow_automizer_transport :
  exists (Q : {group S}) (f : DPFusion.map (val (top c)) Q)
    (hf : DPFusionSystem.allowed F f),
    DPFusion.image f = Q /\ DPFusionSystem.fully_centralized F Q /\
    p.-Sylow(fusion_stabilizer (@transport S F c Q f hf))
      (DPFusionSaturation.ambient_aut_group (val (top (@transport S F c Q f hf))) :&:
        fusion_stabilizer (@transport S F c Q f hf)).
Proof.
have [Q [f [hf [honto [hcent hsyl]]]]] :=
  DPFusionKNormalization.exists_fully_centralized_K_sylow hS sat (fusion_stabilizer_sub c).
exists Q, f, hf; split=> //; split=> //.
by rewrite fusion_stabilizer_transport transport_top_image honto.
Qed.

End Representatives.
End DPNormalizerChainSylowAutomizer.
