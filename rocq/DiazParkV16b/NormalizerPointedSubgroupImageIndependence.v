(** The actual subgroup image is independent of a simultaneous extension
    and its raw orbit representative.  Centric restriction rigidity is proved upstream. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient pgroup boolp.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionCentricRestriction FusionCentricCriterion.
From DiazParkV16b Require Import NormalizerPointedSubgroupExtensions NormalizerPointedSubgroupImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPNormalizerSubgroupExtensions DPNormalizerSubgroupImages.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerSubgroupImageIndependence.
Section Independence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables P Q R T U : {group S}.
Variables f g : DPFusionSystem.arrow F P Q.
Variable a : extension F R T (val f).
Variable b : extension F R U (val g).
Hypothesis cP : DPFusionSystem.centric F P.
Hypothesis cQ : DPFusionSystem.centric F Q.
Hypothesis nPR : P \subset 'N(R).
Hypothesis onto : image (val f) = Q.
Hypothesis eqfg : orbit_class f = orbit_class g.

Theorem image_le_of_orbit_eq : subgroup_image b \subset subgroup_image a.
Proof.
pose V := (P <*> R)%G.
have hVa : V \subset carrier a by rewrite join_subG acting_sub subgroup_sub.
have hVb : V \subset carrier b by rewrite join_subG acting_sub subgroup_sub.
pose fa : DPFusionSystem.arrow F V [set: S]%G :=
  Sub (restrict (extension_map a) hVa)
    (DPFusionSystem.restriction_allowed hVa (extension_allowed a)).
pose fb : DPFusionSystem.arrow F V [set: S]%G :=
  Sub (restrict (extension_map b) hVb)
    (DPFusionSystem.restriction_allowed hVb (extension_allowed b)).
have /orbit_class_eq/exists_inP[r hr /forall_inP he] := eqfg.
have hbig : target_inner fa fb.
  apply (@DPFusionCentricRestriction.centric_inner_restrictions_inner S F p pS sat
    P V [set: S]%G (joing_subl P R) cP fa fb).
  exists r; split; first exact: in_setT.
  move=> x hx; have hv := subsetP (joing_subl P R) _ hx.
  rewrite /arrow_value /fa /fb /= !restrict_in // !on_acting //.
  exact: eqP (he x hx).
have /exists_inP[z _ /forall_inP hz] := hbig.
have hext : {in V, forall x, extension_map b x = (extension_map a x) ^ z}.
  move=> x hx; have hh := eqP (hz x hx).
  by rewrite /arrow_value /fa /fb /= !restrict_in in hh.
have hcentral : z * r^-1 \in 'C(Q).
  apply/centP=> y hy; apply/esym/commgP/conjg_fixP.
  rewrite -onto in hy; have /morphimP[x hx _ ey] := hy.
  rewrite map_morphismE in ey; rewrite ey conjgM.
  have hsame := hext x (subsetP (joing_subl P R) _ hx).
  rewrite !on_acting // in hsame.
  have her : val g x = (val f x) ^ r := eqP (he x hx).
  rewrite -hsame her; exact: conjgK.
have hzQ : z \in Q.
  have hw := subsetP (DPFusionCentricCriterion.centric_self_centralizing cQ) _ hcentral.
  have hh := groupM hw hr; by rewrite mulgKV in hh.
have hn := subsetP (subgroup_image_normalized a nPR onto) _ hzQ.
apply/subsetP=> y /morphimP[x hv hx ->].
rewrite map_morphismE (hext x (subsetP (joing_subr P R) _ hx)) memJ_norm //.
exact: subgroup_image_mem hx.
Qed.

End Independence.

Theorem image_eq_of_orbit_eq (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (P Q R T U : {group S}) (f g : DPFusionSystem.arrow F P Q)
    (a : extension F R T (val f)) (b : extension F R U (val g))
    (cP : DPFusionSystem.centric F P) (cQ : DPFusionSystem.centric F Q)
    (nPR : P \subset 'N(R)) (onto : image (val f) = Q)
    (ontog : image (val g) = Q) (eqfg : orbit_class f = orbit_class g) :
    subgroup_image a = subgroup_image b.
Proof.
apply val_inj; apply/eqP; rewrite eqEsubset.
apply/andP; split.
- exact (@image_le_of_orbit_eq S F p pS sat P Q R U T g f b a cP cQ nPR ontog (esym eqfg)).
- exact (@image_le_of_orbit_eq S F p pS sat P Q R T U f g a b cP cQ nPR onto eqfg).
Qed.
End DPNormalizerSubgroupImageIndependence.
