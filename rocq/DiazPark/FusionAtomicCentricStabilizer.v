From mathcomp Require Import all_ssreflect all_fingroup quotient pgroup sylow nilpotent generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturationImage
  FusionConjugacy FusionOrbit FusionOrbitRanks FusionOuterAutomorphisms
  FusionOuterAction FusionAtomicStabilizer.
Import DPFusion DPFusionOrbit DPFusionOuterAction DPFusionAtomicStabilizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAtomicCentricStabilizer.
Section CentricStabilizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables Q P : {group S}.
Variable raw : DPFusionSystem.arrow F Q P.
Local Notation L := (DPFusion.image (val raw)).
Local Notation N := 'N_P(L)%G.

Lemma centric_image_centralizer : DPFusionSystem.centric F Q -> 'C(L) \subset L.
Proof.
move=> hQ.
have hQL : DPFusionSystem.conjugate F Q L.
  apply/existsP; exists (DPFusion.to_image (val raw)); apply/andP; split.
  - exact: DPFusionSystem.image_closed (valP raw).
  - by rewrite DPFusionSaturationImage.image_to_image.
exact: (implyP (forallP hQ L) hQL).
Qed.

Lemma centric_stabilizer_isog : DPFusionSystem.centric F Q ->
  (N / L) \isog stabilizer (orbit_class raw).
Proof. move=> hQ; exact: stabilizer_isog (centric_image_centralizer hQ). Qed.

Lemma centric_stabilizer_nontrivial (p : nat) :
  p.-group P -> DPFusionSystem.centric F Q -> L \proper P ->
  stabilizer (orbit_class raw) :!=: 1.
Proof.
move=> pP hQ prLP.
have prLN := nilpotent_proper_norm (pgroup_nil pP) prLP.
have nL : N \subset 'N(L) := subsetIr P 'N(L).
have nt : N / L :!=: 1.
  rewrite -subG1 quotient_sub1 //.
  move: prLN; by rewrite properE => /andP[].
by rewrite -(isog_eq1 (centric_stabilizer_isog hQ)).
Qed.

Lemma image_proper_of_no_isomorphism :
  (forall e : @isomorphism (orbit_category F) Q P, False) -> L \proper P.
Proof.
move=> hn; rewrite properEneq DPFusion.image_sub andbT; apply/eqP=> e.
have eG : L = P := val_inj e.
exact: (hn (DPFusionRanks.raw_onto_iso eG)).
Qed.

Theorem atomic_stabilizer_theorem (p : nat) :
  p.-group P -> DPFusionSystem.centric F Q ->
  (N / L) \isog stabilizer (orbit_class raw) /\
  p.-group (stabilizer (orbit_class raw)) /\
  ((forall e : @isomorphism (orbit_category F) Q P, False) ->
    stabilizer (orbit_class raw) :!=: 1).
Proof.
move=> pP hQ; split; first exact: centric_stabilizer_isog hQ.
split; first exact: stabilizer_pgroup pP.
move=> hn; exact: (centric_stabilizer_nontrivial pP hQ (image_proper_of_no_isomorphism hn)).
Qed.
End CentricStabilizer.
Section ActualCentricCategory.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables Q P : DPFusionOrbit.centric_object F.
Variable f : @hom (DPFusionOrbit.centric_orbit_category F) Q P.

Definition centric_isomorphism_of_full
    (e : @isomorphism (orbit_category F) (val Q) (val P)) :
    @isomorphism (centric_orbit_category F) Q P :=
  @Build_isomorphism (centric_orbit_category F) Q P
    (iso_hom e) (iso_inv e) (iso_hom_inv e) (iso_inv_hom e).

Theorem centric_orbit_stabilizer_theorem (p : nat) (pS : p.-group [set: S]) :
  let L := DPFusion.image (val (repr f)) in
  ('N_(val P)(L) / L) \isog stabilizer f /\
  p.-group (stabilizer f) /\
  ((forall e : @isomorphism (centric_orbit_category F) Q P, False) ->
    stabilizer f :!=: 1).
Proof.
move=> L.
have pP : p.-group (val P) := pgroupS (subsetT (val P)) pS.
have [hi [hp hn]] := atomic_stabilizer_theorem (repr f) pP (valP Q).
have ef : orbit_class (repr f) = f := reprK f.
rewrite ef in hi hp hn.
split=> //; split=> // h; apply: hn=> e.
exact: (h (centric_isomorphism_of_full e)).
Qed.
End ActualCentricCategory.
End DPFusionAtomicCentricStabilizer.



