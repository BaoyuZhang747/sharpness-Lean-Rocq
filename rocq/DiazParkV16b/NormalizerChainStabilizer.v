(** The chain stabilizer is an actual subgroup of Aut_F(P_top).  Its
    actual K-normalizer is exactly the simultaneous subgroup normalizer. *)
From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionAutomorphisms GroupKNormalizer.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChain.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module DPNormalizerChainStabilizer.
Section Stabilizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Local Notation P := (val (top c)).
Local Notation I := 'I_(length c).+1.

Definition fusion_stabilizer : {group {perm S}} :=
  (DPFusionSaturation.aut_group F P :&: \bigcap_i 'N(subgroup c i | 'P))%G.

Lemma fusion_stabilizer_sub : fusion_stabilizer \subset DPFusionSaturation.aut_group F P.
Proof. exact: subsetIl. Qed.

Lemma fusion_stabilizerP (a : {perm S}) : reflect
  (a \in DPFusionSaturation.aut_group F P /\
    forall (i : I) x, (a x \in subgroup c i) = (x \in subgroup c i))
  (a \in fusion_stabilizer).
Proof.
apply: (iffP setIP).
- move=> [ha /bigcapP hi]; split=> // i x.
  exact (elimT astabsP (hi i isT) x).
- move=> [ha hi]; split=> //; apply/bigcapP=> i _; apply/astabsP; exact: hi.
Qed.

Lemma normalizer_action_allowed x (hx : x \in 'N(P)) :
  conj_aut P x \in DPFusionSaturation.aut_group F P.
Proof.
apply (subsetP (DPFusionSaturation.ambient_aut_sub F P) _).
rewrite /DPFusionSaturation.ambient_aut_group.
apply/morphimP; exists x=> //.
Qed.

Theorem simultaneous_normalizer_stabilizes x (hx : x \in normalizer c) :
  conj_aut P x \in fusion_stabilizer.
Proof.
have /normalizerP hn := hx.
have ht : x \in 'N(P) := hn ord_max.
have ha := normalizer_action_allowed ht.
apply/fusion_stabilizerP; split=> // i y.
case hy : (y \in P).
- by rewrite norm_conj_autE // memJ_norm // (hn i).
- have haA := subsetP (DPFusionSaturation.aut_group_sub F P) _ ha.
  by rewrite (out_Aut haA (negbT hy)).
Qed.

Theorem stabilizer_normalizes x (hx : x \in 'N(P))
    (ha : conj_aut P x \in fusion_stabilizer) : x \in normalizer c.
Proof.
have /fusion_stabilizerP[_ hfix] := ha.
apply/normalizerP=> i; apply/normP/eqP.
rewrite eqEcard cardJg leqnn andbT.
apply/subsetP=> z /imsetP[y hy ->].
have hyP : y \in P := subsetP (@entry_sub_top S F c i) _ hy.
have he := hfix i y; rewrite norm_conj_autE // in he.
by rewrite he.
Qed.

Theorem normalizer_eq_k_normalizer :
  normalizer c = k_normalizer [set: S]%G P fusion_stabilizer.
Proof.
apply val_inj; apply/setP=> x; apply/idP/morphpreP.
- move=> hx; split.
  + rewrite inE inE /=; exact: subsetP (normalizer_sub_top c) _ hx.
  + change (is_true (conj_aut P x \in fusion_stabilizer)).
    exact: simultaneous_normalizer_stabilizes.
- move=> [hx ha].
  have hxN : x \in 'N(P) by move: hx; rewrite inE inE /=.
  change (is_true (conj_aut P x \in fusion_stabilizer)) in ha.
  exact: stabilizer_normalizes hxN ha.
Qed.

End Stabilizer.
End DPNormalizerChainStabilizer.

Print Assumptions DPNormalizerChainStabilizer.normalizer_eq_k_normalizer.
