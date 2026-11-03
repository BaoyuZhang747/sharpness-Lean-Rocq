From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import FusionMaps FusionSystems FusionAutomorphisms
  FusionOrbit FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientAutomorphisms FusionQuotientCentric FusionQuotientOrbitMaps.
Import DPFusion DPFusionQuotientConstruction DPFusionOrbit
  DPFusionQuotientAutomorphisms DPFusionQuotientCentric DPFusionQuotientOrbitMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientDifference.
Section Difference.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variables P Q : {group coset_of Z}.

(** Equality of induced raw maps has an actual source-kernel factorization,
    before taking target-inner orbit classes. No centricity is assumed. *)
Theorem same_descent_kernel_factorization
    (f g : DPFusionSystem.arrow F (preimage P) (preimage Q))
    (b : DPFusion.map P Q) :
  descends (val f) b -> descends (val g) b ->
  exists gamma : DPFusionSystem.arrow F (preimage P) (preimage P),
    DPFusionAutomorphisms.map_aut (val gamma) \in 'ker (automorphism_morphism cZ P) /\
    DPFusionSystem.arrow_compose gamma f = g.
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
exists (Sub gamma hgamma); split.
- apply: (proj2 (kernel_iff cZ P _)); split.
  + exact: DPFusionAutomorphisms.map_aut_allowed hgamma.
  + move=> x Px; rewrite DPFusionAutomorphisms.map_autE //.
    have gPx : gamma x \in preimage P := DPFusion.map_into gamma Px.
    apply: (DPFusion.map_injective (f := b)).
    * by rewrite -(preimage_mem cZ).
    * by rewrite -(preimage_mem cZ).
    * rewrite (@descendsE S Z P Q (val f) b hf _ gPx) (fgamma x Px).
      exact: esym (@descendsE S Z P Q (val g) b hg x Px).
- apply: val_inj; apply: DPFusion.map_ext=> x Px.
  change (DPFusion.compose gamma (val f) x = val g x).
  by rewrite DPFusion.compose_in // fgamma.
Qed.

Theorem induced_target_inner_adjust
    (f g : DPFusionSystem.arrow F (preimage P) (preimage Q)) :
  target_inner (induced_arrow cZ f) (induced_arrow cZ g) ->
  exists f' : DPFusionSystem.arrow F (preimage P) (preimage Q),
    target_inner f f' /\ descends (val f') (induced_map cZ g).
Proof.
move=> /exists_inP[q Qq /forall_inP he].
pose r := fingroup.repr q.
have rQ : r \in preimage Q := repr_mem cZ Qq.
have Nr : r \in 'N(preimage Q) := subsetP (normG (preimage Q)) r rQ.
have sQQ : preimage Q :^ r \subset preimage Q by rewrite (normP Nr).
pose f' : DPFusionSystem.arrow F (preimage P) (preimage Q) :=
  DPFusionSystem.arrow_compose f
    (Sub (DPFusion.conjugation sQQ) (DPFusionSystem.conjugation_closed F sQQ)).
exists f'; split.
- apply/exists_inP; exists r=> //; apply/forall_inP=> x Px; apply/eqP.
  by rewrite /arrow_value /f' /DPFusionSystem.arrow_compose /=
    DPFusion.compose_in // DPFusion.conjugation_in ?DPFusion.map_into.
- apply/forall_inP=> x Px; apply/eqP.
  have xP : coset Z x \in P by rewrite -(preimage_mem cZ).
  change (arrow_value (induced_arrow cZ g) (coset Z x) = coset Z (val f' x)).
  rewrite (eqP (he _ xP)) (induced_arrowE cZ f Px).
  rewrite /f' /DPFusionSystem.arrow_compose /= DPFusion.compose_in //
    DPFusion.conjugation_in ?DPFusion.map_into //.
  rewrite morphJ ?(normZ_all cZ) //.
  change ((coset Z (val f x)) ^ q = (coset Z (val f x)) ^ coset Z r).
  by rewrite /r coset_reprK.
Qed.
End Difference.
End DPFusionQuotientDifference.

Print Assumptions DPFusionQuotientDifference.same_descent_kernel_factorization.
