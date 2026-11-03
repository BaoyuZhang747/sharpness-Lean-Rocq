From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category ModuleInfrastructure FusionMaps FusionSystems
  FusionOrbit FusionConjugacy FusionAutomorphisms FusionOuterOrbit FusionOrbitRanks
  FusionMackeyShape MackeyStructures MackeyPair MackeyFusionBridge MackeyFusionMinimal
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization
  FusionQuotientAutomorphisms FusionQuotientKernelRestriction.
Import DPFusionOrbit DPFusionMackey DPMackeyFusion DPFusionOuterOrbit
  DPFusionQuotientConstruction DPFusionQuotientNormalization
  DPFusionQuotientAutomorphisms DPFusionQuotientKernelRestriction.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Lemma pair_pull_push_isomorphism (R : comPzRingType) (C : category)
    (M : mackey_pair R C) (P Q : C) (e : isomorphism P Q) x :
  pair_pull M (iso_hom e) (pair_push M (iso_hom e) x) = x.
Proof. by rewrite pair_pull_iso -pair_push_comp iso_hom_inv pair_push_id. Qed.

Lemma pair_pull_identity_of_push_identity (R : comPzRingType) (C : category)
    (M : mackey_pair R C) (P : C) (eh : isomorphism P P) :
    (forall x, pair_push M (iso_hom eh) x = x) ->
    forall x, pair_pull M (iso_hom eh) x = x.
Proof.
move=> he x; rewrite pair_pull_iso.
have hh := @pair_push_comp R C M P P P (iso_inv eh) (iso_hom eh) x.
by rewrite iso_inv_hom pair_push_id he in hh.
Qed.

Module DPFusionMackeyQuotientKernel.
Section KernelTriviality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis hM : inclusion_mackey_formula M.
Let full := full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Hypothesis sZQ : Z \subset Q.

(** This intermediate detection lemma isolates the ordinary minimal-support
    action theorem. The subsequent field wrapper supplies it from the proved
    normal p-subgroup fixed-vector theorem. *)
Hypothesis minimal_kernel_trivial :
  forall (L : {group coset_of Z}), DPFusionSystem.conjugate F Q (preimage L) ->
  forall a, a \in 'ker (automorphism_morphism cZ L) ->
  forall x : pair_value M (preimage L), pair_push M (aut_orbit F (preimage L) a) x = x.

Lemma raw_endomorphism_pull_identity (P : {group S})
    (f : DPFusionSystem.arrow F P P) :
  (forall x, pair_push M (orbit_class f) x = x) ->
  forall x, pair_pull M (orbit_class f) x = x.
Proof.
move=> hf x.
pose e := @DPFusionRanks.raw_onto_iso S F P P f
  (DPFusionAutomorphisms.endomorphism_image (val f)).
exact: (@pair_pull_identity_of_push_identity R (orbit_category F) M P e hf x).
Qed.

Lemma kernel_push_restriction (P L : {group coset_of Z}) (sLP : L \subset P)
    (hQL : DPFusionSystem.conjugate F Q (preimage L)) a
    (aK : a \in 'ker (automorphism_morphism cZ P))
    (x : pair_value M (preimage P)) :
  pair_pull M (orbit_class (inclusion_arrow F (preimage_sub sLP)))
    (pair_push M (aut_orbit F (preimage P) a) x) =
  pair_pull M (orbit_class (inclusion_arrow F (preimage_sub sLP))) x.
Proof.
pose aa := @restricted_arrow S F Z cZ L P sLP a aK.
have hpush : forall y, pair_push M (orbit_class aa) y = y.
  move=> y; rewrite -map_aut_orbit.
  exact: (@minimal_kernel_trivial L hQL _
    (@restricted_kernel S F Z cZ L P sLP a aK) y).
have hpull := raw_endomorphism_pull_identity hpush.
have ht := congr1 (fun f => pair_pull M f
    (pair_push M (aut_orbit F (preimage P) a) x))
  (@restriction_triangle S F Z cZ L P sLP a aK).
rewrite !pair_pull_comp hpull in ht.
pose e := @DPFusionRanks.raw_onto_iso S F (preimage P) (preimage P) (aut_arrow F (preimage P) a)
  (DPFusionAutomorphisms.endomorphism_image _).
have hi : pair_pull M (aut_orbit F (preimage P) a)
    (pair_push M (aut_orbit F (preimage P) a) x) = x.
  exact: (@pair_pull_push_isomorphism R (orbit_category F) M _ _ e x).
by rewrite hi in ht.
Qed.

Theorem kernel_push_trivial (P : {group coset_of Z}) a
    (aK : a \in 'ker (automorphism_morphism cZ P))
    (x : pair_value M (preimage P)) :
  pair_push M (aut_orbit F (preimage P) a) x = x.
Proof.
apply: (@DPMackeyMinimal.inclusion_restriction_injective S F R full Q leastQ simple
  (preimage P) (pair_push M (aut_orbit F (preimage P) a) x) x).
move=> L sLP hQL.
have sZL := conjugate_contains_kernel cZ sZQ hQL.
have eL := preimage_of_quotient cZ sZL.
have hbar : (L / Z)%G \subset P.
  have h : (L / Z)%G \subset (preimage P / Z)%G := quotientS Z sLP.
  by rewrite preimage_quotient in h.
have hqbar : DPFusionSystem.conjugate F Q (preimage (L / Z)%G) by rewrite eL.
have h := kernel_push_restriction hbar hqbar aK x.
move: h; generalize (preimage_sub hbar).
rewrite eL=> hs h.
have eh : hs = sLP by apply: bool_irrelevance.
by rewrite eh in h.
Qed.

Theorem kernel_pull_trivial (P : {group coset_of Z}) a
    (aK : a \in 'ker (automorphism_morphism cZ P))
    (x : pair_value M (preimage P)) :
  pair_pull M (aut_orbit F (preimage P) a) x = x.
Proof.
apply: (@raw_endomorphism_pull_identity (preimage P) (aut_arrow F (preimage P) a)).
exact: kernel_push_trivial aK.
Qed.
End KernelTriviality.
End DPFusionMackeyQuotientKernel.
