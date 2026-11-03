From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionAutomorphisms
  FusionOrbit FusionOuterOrbit MackeyStructures MackeyPair
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientAutomorphisms
  FusionQuotientOrbitMaps FusionQuotientDifference FusionQuotientKernelRestriction
  FusionMackeyQuotientKernel.
Import DPFusionOrbit DPFusionOuterOrbit DPFusionQuotientConstruction
  DPFusionQuotientAutomorphisms DPFusionQuotientOrbitMaps
  DPFusionQuotientDifference DPFusionQuotientKernelRestriction.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientIndependence.
Section Independence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis kernel_trivial : forall (P : {group coset_of Z}) a,
  a \in 'ker (automorphism_morphism cZ P) ->
  forall x : pair_value M (preimage P), pair_push M (aut_orbit F (preimage P) a) x = x.

Lemma raw_kernel_push (P : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage P)) :
  DPFusionAutomorphisms.map_aut (val f) \in 'ker (automorphism_morphism cZ P) ->
  forall x, pair_push M (orbit_class f) x = x.
Proof. move=> h x; rewrite -map_aut_orbit; exact: (@kernel_trivial P _ h x). Qed.

Lemma raw_kernel_pull (P : {group coset_of Z})
    (f : DPFusionSystem.arrow F (preimage P) (preimage P)) :
  DPFusionAutomorphisms.map_aut (val f) \in 'ker (automorphism_morphism cZ P) ->
  forall x, pair_pull M (orbit_class f) x = x.
Proof.
move=> h; apply: DPFusionMackeyQuotientKernel.raw_endomorphism_pull_identity.
exact: raw_kernel_push h.
Qed.

Theorem same_descent_coefficients (P Q : {group coset_of Z})
    (f g : DPFusionSystem.arrow F (preimage P) (preimage Q)) (b : DPFusion.map P Q) :
  descends (val f) b -> descends (val g) b ->
  (forall x, pair_push M (orbit_class g) x = pair_push M (orbit_class f) x) /\
  (forall y, pair_pull M (orbit_class g) y = pair_pull M (orbit_class f) y).
Proof.
move=> hf hg.
have [gamma [hK he]] := same_descent_kernel_factorization cZ hf hg.
have ho : orbit_class g = orbit_compose (orbit_class gamma) (orbit_class f).
  by rewrite orbit_compose_class he.
split=> x; rewrite ho.
- by rewrite pair_push_comp (raw_kernel_push hK).
- by rewrite pair_pull_comp (raw_kernel_pull hK).
Qed.

Theorem induced_inner_coefficients (P Q : {group coset_of Z})
    (f g : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
  target_inner (induced_arrow cZ f) (induced_arrow cZ g) ->
  (forall x, pair_push M (orbit_class g) x = pair_push M (orbit_class f) x) /\
  (forall y, pair_pull M (orbit_class g) y = pair_pull M (orbit_class f) y).
Proof.
move=> hi.
have [f' [hf' hd]] := induced_target_inner_adjust hi.
have he : orbit_class f = orbit_class f' by apply/orbit_class_eq.
have h := same_descent_coefficients hd (induced_map_descends cZ g).
by rewrite -he in h.
Qed.

Theorem orbit_map_coefficients (P Q : {group coset_of Z})
    (f g : orbit_hom F (preimage P) (preimage Q)) :
  orbit_map cZ f = orbit_map cZ g ->
  (forall x, pair_push M g x = pair_push M f x) /\
  (forall y, pair_pull M g y = pair_pull M f y).
Proof.
move=> he.
have hi : target_inner (induced_arrow cZ (repr f)) (induced_arrow cZ (repr g)).
  apply/orbit_class_eq; exact: he.
have h := induced_inner_coefficients hi.
by rewrite /orbit_class !reprK in h.
Qed.
End Independence.
End DPFusionMackeyQuotientIndependence.
