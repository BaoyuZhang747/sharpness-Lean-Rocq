From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionAutomorphisms FusionOrbit FusionOuterOrbit FusionMackeyShape
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientAutomorphisms
  FusionQuotientCentric.
Import DPFusion DPFusionOrbit DPFusionOuterOrbit DPFusionQuotientConstruction
  DPFusionQuotientAutomorphisms DPFusionQuotientCentric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientKernelRestriction.
Section Restriction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variables L P : {group coset_of Z}.
Hypothesis sLP : L \subset P.
Variable a : {perm S}.
Hypothesis aK : a \in 'ker (automorphism_morphism cZ P).

Lemma preimage_sub : preimage L \subset preimage P.
Proof. exact: morphpreS. Qed.

Lemma kernel_allowed : a \in DPFusionSaturation.aut_group F (preimage P).
Proof. exact: (proj1 (kernel_iff cZ P a) aK).1. Qed.

Lemma preserves_subgroup x : x \in preimage L -> a x \in preimage L.
Proof.
move=> Lx.
have Px := subsetP preimage_sub x Lx.
rewrite (preimage_mem cZ) ((proj1 (kernel_iff cZ P a) aK).2 x Px).
by move: Lx; rewrite (preimage_mem cZ).
Qed.

Lemma restricted_image :
  DPFusion.image (DPFusion.restrict (aut_map F (preimage P) a) preimage_sub) \subset preimage L.
Proof.
apply/subsetP=> y /morphimP[x Lx _ ->].
change (is_true (DPFusion.restrict (aut_map F (preimage P) a) preimage_sub x \in preimage L)).
rewrite DPFusion.restrict_in // aut_mapE ?kernel_allowed ?(subsetP preimage_sub _ Lx) //.
exact: preserves_subgroup.
Qed.

Definition restricted_map : DPFusion.map (preimage L) (preimage L) :=
  DPFusion.corestrict restricted_image.

Lemma restricted_mapE : {in preimage L, restricted_map =1 a}.
Proof.
move=> x Lx; rewrite /restricted_map DPFusion.corestrict_in // DPFusion.restrict_in //.
exact: (@aut_mapE S F (preimage P) a kernel_allowed x (subsetP preimage_sub x Lx)).
Qed.

Lemma restricted_allowed : DPFusionSystem.allowed F restricted_map.
Proof.
apply: DPFusionSystem.corestriction_allowed.
apply: DPFusionSystem.restriction_allowed.
exact: aut_map_allowed.
Qed.

Definition restricted_arrow : DPFusionSystem.arrow F (preimage L) (preimage L) :=
  Sub restricted_map restricted_allowed.

Lemma restricted_kernel :
  DPFusionAutomorphisms.map_aut restricted_map \in 'ker (automorphism_morphism cZ L).
Proof.
apply: (proj2 (kernel_iff cZ L _)); split.
- exact: DPFusionAutomorphisms.map_aut_allowed restricted_allowed.
- move=> x Lx; rewrite DPFusionAutomorphisms.map_autE // restricted_mapE //.
  exact: (proj1 (kernel_iff cZ P a) aK).2 x (subsetP preimage_sub x Lx).
Qed.

Lemma restriction_triangle :
  orbit_compose (orbit_class restricted_arrow)
    (orbit_class (DPFusionMackey.inclusion_arrow F preimage_sub)) =
  orbit_compose (orbit_class (DPFusionMackey.inclusion_arrow F preimage_sub))
    (aut_orbit F (preimage P) a).
Proof.
rewrite /aut_orbit !orbit_compose_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Lx.
change (DPFusion.compose restricted_map (DPFusion.inclusion preimage_sub) x =
  DPFusion.compose (DPFusion.inclusion preimage_sub) (aut_map F (preimage P) a) x).
rewrite !DPFusion.compose_in // !DPFusion.inclusion_in ?DPFusion.map_into //.
by rewrite restricted_mapE // aut_mapE ?kernel_allowed ?(subsetP preimage_sub x Lx).
Qed.
End Restriction.

Section RawAutomorphism.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : {group S}.

Lemma map_aut_orbit (f : DPFusionSystem.arrow F P P) :
  aut_orbit F P (DPFusionAutomorphisms.map_aut (val f)) = orbit_class f.
Proof.
rewrite /aut_orbit.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Px.
change (aut_map F P (DPFusionAutomorphisms.map_aut (val f)) x = val f x).
by rewrite aut_mapE ?DPFusionAutomorphisms.map_aut_allowed ?(valP f) //
  DPFusionAutomorphisms.map_autE.
Qed.
End RawAutomorphism.
End DPFusionQuotientKernelRestriction.

Print Assumptions DPFusionQuotientKernelRestriction.restricted_kernel.
Print Assumptions DPFusionQuotientKernelRestriction.restriction_triangle.
