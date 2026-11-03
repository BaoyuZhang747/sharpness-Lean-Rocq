(** The actual pointing has the universal factorization property.  This
    follows from literal selected-chain inverse extensions and faithful orbit
    maps, rather than an assumed reflection or comma-cofinality theorem. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks FusionConjugacy.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices NormalizerChainExtensions
  NormalizerProjectionCommaSelection NormalizerProjectionCommaInverse
  NormalizerOrbitPairCategory NormalizerOrbitSameChainCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPFusionConjugacy DPLinkingChains DPNormalizerChainIndices
  DPNormalizerChainExtensions DPNormalizerProjectionCommaSelection DPNormalizerProjectionCommaInverse
  DPNormalizerOrbitPair.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaFactorization.
Section Extensions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variables P Q U : {group S}.
Variable f : DPFusion.map P Q.
Variable g : DPFusion.map P U.
Variable a : extension c d f.
Variable b : extension c d g.
Variable onto : image f = Q.

Definition factor_extension : extension d d (DPFusion.compose (onto_inverse onto) g).
Proof.
have b' : extension (selected_chain (indices a)) d g.
  rewrite (indices_unique a b); exact: on_selected b.
exact (compose_extension (inverse_selected a onto) b').
Defined.
End Extensions.

Section Universal.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable A : DPNormalizerOrbitPair.object F.
Variable d : chain F.
Variables B C : DPNormalizerOrbitSameChain.object d.
Local Notation Bp := (DPNormalizerOrbitSameChain.point B).
Local Notation Cp := (DPNormalizerOrbitSameChain.point C).
Variable u : pair_hom A Bp.
Variable z : @isomorphism (centric_orbit_category F) (acting A) (acting Bp).
Variable hz : iso_hom z = val u.

Theorem pointing_factorization (f : pair_hom A Cp) :
  exists! g : pair_hom Bp Cp, pair_compose u g = f.
Proof.
have [u0 [hu [a]]] := hom_compatible u.
have [f0 [hf [b]]] := hom_compatible f.
have hcard : #|val (acting A)| = #|val (acting Bp)|.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - exact: DPFusionRanks.orbit_rank_le (val u).
  - exact: DPFusionRanks.orbit_rank_le (iso_inv z).
have ho : image (val u0) = val (acting Bp) := DPFusionRanks.raw_equal_rank_image u0 hcard.
pose g0 : DPFusionSystem.arrow F (val (acting Bp)) (val (acting Cp)) :=
  Sub (DPFusion.compose (onto_inverse ho) (val f0))
    (DPFusionSystem.composition_closed (onto_inverse_allowed ho (valP u0)) (valP f0)).
pose a0 : extension d d (val g0) := factor_extension a b ho.
pose g := @hom_of_extension S F Bp Cp g0 a0.
have he : DPFusionSystem.arrow_compose u0 g0 = f0.
  apply val_inj; apply: map_ext=> x hx.
  change (DPFusion.compose (val u0) (DPFusion.compose (onto_inverse ho) (val f0)) x = val f0 x).
  by rewrite !compose_in ?map_into // onto_inverse_cancel.
have hg : pair_compose u g = f.
  apply val_inj; change (orbit_compose (val u) (orbit_class g0) = val f).
  by rewrite -hu -hf orbit_compose_class he.
exists g; split=> // g' hg'.
apply val_inj.
have h := congr1 (fun k : pair_hom A Cp => val k) (eq_trans hg' (esym hg)).
change (@Category.compose (centric_orbit_category F) (acting A) (acting Bp) (acting Cp)
  (val u) (val g') = @Category.compose (centric_orbit_category F)
    (acting A) (acting Bp) (acting Cp) (val u) (val g)) in h.
rewrite -hz in h.
have hh := congr1 (fun k : hom (centric_orbit_category F) (acting A) (acting Cp) =>
  Category.compose (iso_inv z) k) h.
by rewrite -!Category.compose_assoc (iso_inv_hom z) !Category.compose_id_left in hh.
Qed.
End Universal.
End DPNormalizerProjectionCommaFactorization.
