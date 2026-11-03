(** Actual pointing to a fixed Sylow chain representative. The arrow is a
    genuine pair arrow and is an isomorphism on its acting centric subgroups. *)
From mathcomp Require Import all_boot all_fingroup pgroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionSaturation FusionSaturationImage FusionCentricBasics.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer
  NormalizerChainIndices NormalizerChainExtensions NormalizerChainRelations
  NormalizerChainConjugacy NormalizerChainSubconjugacy NormalizerChainStabilizer
  NormalizerProjectionCommaChainExtension NormalizerOrbitPairCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPLinkingChains DPNormalizerChain
  DPNormalizerChainIndices DPNormalizerChainExtensions DPNormalizerChainRelations
  DPNormalizerChainConjugacy DPNormalizerChainStabilizer
  DPNormalizerProjectionCommaChainExtension DPNormalizerOrbitPair.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaPointing.
Section Pointing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable A : DPNormalizerOrbitPair.object F.
Variable d : chain F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable sylD : p.-Sylow(fusion_stabilizer d)
  (DPFusionSaturation.ambient_aut_group (val (top d)) :&: fusion_stabilizer d).

Lemma normalizer_selected (e : selector (chain_of A) d) :
  normalizer (chain_of A) \subset normalizer (selected_chain e).
Proof.
apply/subsetP=> x /normalizerP hx; apply/normalizerP=> i.
rewrite /subgroup selected_chain_entry; exact: hx.
Qed.

Theorem exists_raw_pointing_of_selected (e : selector (chain_of A) d)
    (hc : conjugate (selected_chain e) d) :
  exists B : DPNormalizerOrbitPair.object F, chain_of B = d /\
    exists f : DPFusionSystem.arrow F (val (acting A)) (val (acting B)),
      image (val f) = val (acting B) /\ inhabited (extension (chain_of A) (chain_of B) (val f)).
Proof.
have /conjugateP[a ba] := hc.
have [V [g [hTop [hNorm [hg him]]]]] :=
  @chain_conjugacy_normalizer_extension S F (selected_chain e) d a ba p hS sat sylD.
have hPV : val (acting A) \subset V :=
  subset_trans (acting_normalizes A) (subset_trans (normalizer_selected e) hNorm).
pose r := restrict g hPV.
have hr : DPFusionSystem.allowed F r := DPFusionSystem.restriction_allowed hPV hg.
have hcQ : DPFusionSystem.centric F (image r) := DPFusionCentricBasics.centric_image hr (valP (acting A)).
pose Q : centric_object F := Sub (image r) hcQ.
have hQN : val Q \subset normalizer d.
  apply/subsetP=> y /morphimP[x _ hx ->].
  rewrite map_morphismE /r restrict_in //; apply/normalizerP=> i.
  rewrite -(him i).
  apply (subsetP (morphim_norm (map_morphism g) (subgroup (selected_chain e) (index (indices a) i)))).
  apply/morphimP; exists x; first exact: subsetP hPV _ hx.
  - rewrite /subgroup selected_chain_entry.
    exact (elimT (normalizerP _ _) (subsetP (acting_normalizes A) _ hx) _).
  - reflexivity.
pose B : DPNormalizerOrbitPair.object F := Sub (Q, d) hQN.
pose f : DPFusionSystem.arrow F (val (acting A)) (val Q) :=
  Sub (to_image r) (DPFusionSystem.image_closed hr).
exists B; split; first reflexivity.
exists f; split; first exact: DPFusionSaturationImage.image_to_image.
apply: inhabits.
refine (@Build_extension S F (chain_of A) d (val (acting A)) (val Q) (val f)
  (DPNormalizerChainIndices.compose e (indices a)) V hPV _ g hg _ _).
- rewrite compose_index.
  have ht := subset_trans (@entry_sub_top S F (selected_chain e) (index (indices a) ord_max)) hTop.
  by rewrite /subgroup selected_chain_entry in ht.
- move=> x hx; by rewrite /f /= to_image_in // /r restrict_in.
- move=> i; rewrite compose_index.
  have hi := him i; by rewrite /subgroup selected_chain_entry in hi.
Qed.

Definition centric_raw_onto_iso (P Q : centric_object F)
    (f : DPFusionSystem.arrow F (val P) (val Q)) (ho : image (val f) = val Q) :
    @isomorphism (centric_orbit_category F) P Q.
Proof.
pose e := DPFusionRanks.raw_onto_iso ho.
exact (@Build_isomorphism (centric_orbit_category F) P Q
  (iso_hom e) (iso_inv e) (iso_hom_inv e) (iso_inv_hom e)).
Defined.

Theorem exists_pointing_of_subconjugate (h : subconjugate (chain_of A) d) :
  exists B : DPNormalizerOrbitPair.object F, chain_of B = d /\
    exists u : pair_hom A B, exists z : @isomorphism (centric_orbit_category F) (acting A) (acting B),
      iso_hom z = fmap (forget F) u.
Proof.
have [e he] := proj1 (DPNormalizerChainSubconjugacy.subconjugate_selected_iff _ _) h.
have [B [hB [f [hf [a]]]]] := exists_raw_pointing_of_selected he.
exists B; split=> //; exists (hom_of_extension a), (centric_raw_onto_iso hf); reflexivity.
Qed.
End Pointing.
End DPNormalizerProjectionCommaPointing.
