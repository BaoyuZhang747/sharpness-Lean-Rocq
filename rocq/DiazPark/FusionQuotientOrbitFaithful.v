From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionSaturation FusionAutomorphisms FusionQuotientMaps
  FusionQuotientConstruction FusionQuotientAutomorphisms FusionQuotientCentric
  FusionQuotientCentricTransport FusionQuotientOrbitMaps.
Import DPFusion DPFusionQuotientConstruction DPFusionOrbit
  DPFusionQuotientAutomorphisms DPFusionQuotientCentric
  DPFusionQuotientCentricTransport DPFusionQuotientOrbitMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionQuotientOrbitFaithful.
Section Faithfulness.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pZ : p.-group Z.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables P Q : {group coset_of Z}.
Hypothesis hP : DPFusionSystem.centric (system cZ) P.

Lemma same_descent_target_inner
    (f g : DPFusionSystem.arrow F (preimage P) (preimage Q))
    (b : DPFusion.map P Q) :
  descends (val f) b -> descends (val g) b -> target_inner f g.
Proof.
move=> hf hg.
have imEq : DPFusion.image (val g) = DPFusion.image (val f).
  by rewrite (descends_image_preimage cZ (valP g) hg)
    (descends_image_preimage cZ (valP f) hf).
have sIf : DPFusion.image (val g) \subset DPFusion.image (val f) by rewrite imEq.
pose gamma := DPFusion.compose (DPFusion.corestrict sIf) (DPFusion.inverse (val f)).
have hgamma : DPFusionSystem.allowed F gamma.
  apply: DPFusionSystem.composition_closed.
  - exact: DPFusionSystem.corestriction_allowed (valP g).
  - exact: DPFusionSystem.inverse_closed (valP f).
have fgamma : {in preimage P, forall x, val f (gamma x) = val g x}.
  move=> x Px; rewrite /gamma DPFusion.compose_in // DPFusion.corestrict_in //.
  apply: DPFusion.inverse_cancel_right.
  by rewrite -imEq; exact: DPFusion.image_mem.
pose a := DPFusionAutomorphisms.map_aut gamma.
have aA := DPFusionAutomorphisms.map_aut_allowed hgamma.
have aK : a \in 'ker (automorphism_morphism cZ P).
  apply: (proj2 (kernel_iff cZ P a)); split=> // x Px.
  rewrite /a DPFusionAutomorphisms.map_autE //.
  have gPx : gamma x \in preimage P := DPFusion.map_into gamma Px.
  apply: (DPFusion.map_injective (f := b)).
  - by rewrite -(preimage_mem cZ).
  - by rewrite -(preimage_mem cZ).
  - rewrite (@descendsE S Z P Q (val f) b hf _ gPx) (fgamma x Px).
    exact: esym (@descendsE S Z P Q (val g) b hg x Px).
have aI := subsetP (@centric_kernel_inner S F Z cZ P p pZ sat hP) a aK.
have /morphimP[r Nr Pr ea] := aI.
have egamma : {in preimage P, forall x, gamma x = x ^ r}.
  move=> x Px.
  rewrite -(@DPFusionAutomorphisms.map_autE S (preimage P) gamma x Px).
  change (a x = x ^ r).
  by rewrite ea norm_conj_autE.
apply/exists_inP; exists (val f r); first exact: DPFusion.map_into Pr.
apply/forall_inP=> x Px; apply/eqP.
change (val g x = (val f x) ^ (val f r)).
rewrite -(fgamma x Px) (egamma x Px).
exact: (@morphJ S S (preimage P) (DPFusion.map_morphism (val f)) x r Px Pr).
Qed.

Lemma induced_target_inner_reflect
    (f g : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
  target_inner (induced_arrow cZ f) (induced_arrow cZ g) -> target_inner f g.
Proof.
move=> /exists_inP[q Qq /forall_inP he].
pose r := fingroup.repr q.
have rQ : r \in preimage Q := repr_mem cZ Qq.
have Nr : r \in 'N(preimage Q) := subsetP (normG (preimage Q)) r rQ.
have sQQ : preimage Q :^ r \subset preimage Q by rewrite (normP Nr).
pose f' : DPFusionSystem.arrow F (preimage P) (preimage Q) :=
  DPFusionSystem.arrow_compose f
    (Sub (DPFusion.conjugation sQQ) (DPFusionSystem.conjugation_closed F sQQ)).
have hff : target_inner f f'.
  apply/exists_inP; exists r=> //; apply/forall_inP=> x Px; apply/eqP.
  by rewrite /arrow_value /f' /DPFusionSystem.arrow_compose /=
    DPFusion.compose_in // DPFusion.conjugation_in ?DPFusion.map_into.
have hf' : descends (val f') (induced_map cZ g).
  apply/forall_inP=> x Px; apply/eqP.
  have xP : coset Z x \in P by rewrite -(preimage_mem cZ).
  change (arrow_value (induced_arrow cZ g) (coset Z x) = coset Z (val f' x)).
  rewrite (eqP (he _ xP)) (induced_arrowE cZ f Px).
  rewrite /f' /DPFusionSystem.arrow_compose /= DPFusion.compose_in //
    DPFusion.conjugation_in ?DPFusion.map_into //.
  rewrite morphJ ?(normZ_all cZ) //.
  change (coset Z (val f x) ^ q = coset Z (val f x) ^ coset Z r).
  by rewrite /r coset_reprK.
have hf'g := same_descent_target_inner hf' (induced_map_descends cZ g).
exact: target_inner_trans hff hf'g.
Qed.

Theorem orbit_map_injective :
  injective (@DPFusionQuotientOrbitMaps.orbit_map S F Z cZ P Q).
Proof.
move=> f g he.
have hi : target_inner (induced_arrow cZ (repr f)) (induced_arrow cZ (repr g)).
  apply/orbit_class_eq; exact: he.
have hf : orbit_class (repr f) = orbit_class (repr g).
  apply/orbit_class_eq; exact: induced_target_inner_reflect hi.
by rewrite /orbit_class !reprK in hf.
Qed.

End Faithfulness.
End DPFusionQuotientOrbitFaithful.

Print Assumptions DPFusionQuotientOrbitFaithful.same_descent_target_inner.
Print Assumptions DPFusionQuotientOrbitFaithful.induced_target_inner_reflect.
Print Assumptions DPFusionQuotientOrbitFaithful.orbit_map_injective.
