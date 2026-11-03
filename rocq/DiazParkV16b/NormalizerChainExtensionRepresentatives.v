(** Simultaneous chain extensions survive actual target-inner changes of
    orbit representatives.  The target acting group normalizes every entry. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainExtensions NormalizerChainNormalizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChainIndices DPNormalizerChainExtensions.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerChainExtensionRepresentatives.
Section Representatives.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition change_codomain (c d : chain F) (P Q T : {group S})
    (f : DPFusion.map P Q) (g : DPFusion.map P T) (a : extension c d f)
    (he : {in P, f =1 g}) : extension c d g.
Proof.
refine (@Build_extension S F c d P T g (indices a) (carrier a)
  (acting_sub a) (chain_sub a) (extension_map a) (extension_allowed a) _ (entry_images a)).
move=> x hx; by rewrite on_acting // he.
Defined.

Definition inclusion_extension (P Q : {group S}) (h : P \subset Q) (c : chain F) :
  extension c c (DPFusion.inclusion h).
Proof.
apply: (change_codomain (identity_extension P c)).
move=> x hx; by rewrite identity_in // inclusion_in.
Defined.

Definition conjugated_map (V : {group S}) (b : DPFusion.map V [set: S]%G) (z : S) :
  DPFusion.map V [set: S]%G :=
  DPFusion.compose b (DPFusion.conjugation (subsetT ([set: S] :^ z))).

Lemma conjugated_mapE (V : {group S}) (b : DPFusion.map V [set: S]%G) z x :
  x \in V -> conjugated_map b z x = (b x) ^ z.
Proof. move=> hx; by rewrite /conjugated_map compose_in // conjugation_in ?map_into. Qed.

Definition conjugate_extension (c d : chain F) (P Q : {group S})
    (f g : DPFusion.map P Q) (a : extension c d f) (z : S)
    (hz : z \in DPNormalizerChain.normalizer d)
    (he : {in P, forall x, g x = (f x) ^ z}) : extension c d g.
Proof.
pose b := conjugated_map (extension_map a) z.
refine (@Build_extension S F c d P Q g (indices a) (carrier a)
  (acting_sub a) (chain_sub a) b _ _ _).
- apply: DPFusionSystem.composition_closed (extension_allowed a) _.
  exact: DPFusionSystem.conjugation_closed.
- move=> x hx; rewrite /b conjugated_mapE ?(subsetP (acting_sub a) _ hx) //.
  by rewrite on_acting // he.
- move=> i; have hzi := subsetP (@DPNormalizerChain.normalizer_sub S F d i) _ hz.
  apply/setP=> y; apply/morphimP/idP.
  + move=> [x hv hx ->]; rewrite map_morphismE /b conjugated_mapE //.
    rewrite -(normP hzi) mem_conjg conjgK.
    rewrite -(entry_images a i); exact: mem_morphim hv hx.
  + move=> hy.
    have hzy : y ^ z^-1 \in subgroup d i.
      have hzvi : z^-1 \in 'N(subgroup d i) by rewrite groupV.
      by rewrite -(normP hzvi) mem_conjg conjgK.
    rewrite -(entry_images a i) in hzy.
    have /morphimP[x hv hx ex] := hzy.
    rewrite map_morphismE in ex.
    exists x=> //; rewrite map_morphismE /b conjugated_mapE // -ex.
    by rewrite conjgKV.
Defined.

Definition of_orbit_eq (c d : chain F) (P Q : {group S})
    (hQ : Q \subset DPNormalizerChain.normalizer d)
    (f g : DPFusionSystem.arrow F P Q) (a : extension c d (val f))
    (he : DPFusionOrbit.orbit_class f = DPFusionOrbit.orbit_class g) :
    extension c d (val g).
Proof.
have hex : exists z : S, z \in Q /\ {in P, forall x, val g x = (val f x) ^ z}.
  have /DPFusionOrbit.orbit_class_eq/exists_inP[z hz /forall_inP hez] := he.
  exists z; split=> //; move=> x hx; exact: eqP (hez x hx).
have [z [hz hez]] := cid hex.
exact (conjugate_extension a (subsetP hQ _ hz) hez).
Defined.
End Representatives.
End DPNormalizerChainExtensionRepresentatives.
