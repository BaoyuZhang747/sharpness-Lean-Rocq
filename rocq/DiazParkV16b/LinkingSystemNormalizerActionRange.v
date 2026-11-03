(** The range condition for a linking normalizer extension is closed
    under adjoining the centric top subgroup. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemAutomorphisms NormalizerChainTransporter LinkingSystemNormalizerExtensionLift.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingAutomorphisms
  DPNormalizerChainTransporter DPLinkingNormalizerExtensionLift.
Local Open Scope group_scope.

Module DPLinkingNormalizerActionRange.
Section Range.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable U : DPFusionOrbit.centric_object F.

Definition normalizer_action (H : {group S}) (hH : H \subset 'N(val U))
    (x : [subg H]) : automorphism_group L U :=
  normalizer_map L (Sub (val x) (subsetP hH _ (valP x))).

Lemma normalizer_action_eq (H J : {group S})
    (hH : H \subset 'N(val U)) (hJ : J \subset 'N(val U))
    (x : [subg H]) (y : [subg J]) : val x = val y ->
    normalizer_action hH x = normalizer_action hJ y.
Proof.
move=> he; rewrite /normalizer_action; congr (normalizer_map L _); apply val_inj; exact he.
Qed.

Lemma normalizer_action_mul (H : {group S}) (hH : H \subset 'N(val U))
    (x y : [subg H]) :
    normalizer_action hH (x * y) = normalizer_action hH x * normalizer_action hH y.
Proof.
rewrite /normalizer_action -normalizer_map_mul.
congr (normalizer_map L _); apply val_inj; reflexivity.
Qed.

Lemma normalizer_action_inner (x : [subg (val U)]) :
  normalizer_action (normG (val U)) x = distinguished L x.
Proof.
rewrite /normalizer_action /normalizer_map /distinguished.
congr (linking_transporter L _); apply val_inj; reflexivity.
Qed.

Lemma distinguished_conjugation (a : automorphism_group L U) (x : [subg (val U)]) :
  distinguished L (arrow_element (linking_projection L a) x) =
    (distinguished L x : automorphism_group L U) ^ a.
Proof.
have he := @commutation S F L U U a x.
change ((distinguished L x : automorphism_group L U) * a =
  a * distinguished L (arrow_element (linking_projection L a) x)) in he.
have hm := congr1 (fun z : automorphism_group L U => a^-1 * z) he.
rewrite !mulgA mulVg mul1g in hm; rewrite /conjg mulgA; exact (esym hm).
Qed.

Variables P : {group S}.
Variable T : DPFusionOrbit.centric_object F.
Hypothesis hP : P \subset 'N(val U).
Hypothesis hUT : val U \subset val T.
Hypothesis hT : val T \subset 'N(val U).
Variable a : automorphism_group L U.
Hypothesis rangeP : forall x : [subg P], exists y : [subg (val T)],
  normalizer_action hT y = normalizer_action hP x ^ a.

Lemma join_normalizes : val U <*> P \subset 'N(val U).
Proof. by rewrite join_subG normG hP. Qed.

Theorem join_action_range : forall x : [subg (val U <*> P)%G],
  exists y : [subg (val T)], normalizer_action hT y = normalizer_action join_normalizes x ^ a.
Proof.
move=> x.
have hx := valP x.
change (is_true (val x \in val U <*> P)) in hx.
rewrite (norm_joinEr hP) in hx.
have /mulsgP [u v hu hv huv] := hx.
pose ux : [subg (val U)] := Sub u hu.
pose vx : [subg P] := Sub v hv.
have [y2 hy2] := rangeP vx.
pose y1 := overgroup_element hUT (arrow_element (linking_projection L a) ux).
exists (y1 * y2); rewrite normalizer_action_mul hy2.
have hy1 : normalizer_action hT y1 = normalizer_action (normG (val U)) ux ^ a.
  transitivity (normalizer_action (normG (val U)) (arrow_element (linking_projection L a) ux)).
  - apply: normalizer_action_eq; reflexivity.
  - rewrite !normalizer_action_inner; exact: distinguished_conjugation.
rewrite hy1 -conjMg.
congr (_ ^ a).
rewrite /normalizer_action -normalizer_map_mul.
congr (normalizer_map L _); apply val_inj; exact: esym huv.
Qed.
End Range.
End DPLinkingNormalizerActionRange.

Check DPLinkingNormalizerActionRange.join_action_range.
Print Assumptions DPLinkingNormalizerActionRange.join_action_range.
