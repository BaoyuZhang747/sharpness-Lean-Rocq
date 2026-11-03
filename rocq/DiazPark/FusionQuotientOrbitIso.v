From mathcomp Require Import all_ssreflect all_fingroup generic_quotient pgroup boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex FusionMaps FusionSystems
  FusionOrbit FusionSaturation FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientNormalization FusionQuotientOrbitMaps FusionQuotientOrbitFaithful.
Import DPFusion DPFusionQuotientConstruction DPFusionOrbit
  DPFusionQuotientOrbitMaps DPFusionQuotientOrbitFaithful.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionQuotientOrbitIso.
Section Isomorphism.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pZ : p.-group Z.
Hypothesis sat : DPFusionSaturation.saturated F p.

(** Objects are literally quotient-centric subgroups, whose associated
    ambient objects are their unique full preimages. *)
Definition preimage_category : category :=
  reindexed_category (orbit_category F)
    (fun P : centric_object (system cZ) => preimage (val P)).

Definition quotient_functor : functor preimage_category (centric_orbit_category (system cZ)).
Proof.
refine (@Build_functor preimage_category (centric_orbit_category (system cZ))
  (fun P => P) (fun P Q f => orbit_map cZ f) _ _).
- move=> P; exact: orbit_map_identity.
- move=> P Q R f g; exact: orbit_map_compose.
Defined.

Lemma lift_orbit_exists (P Q : centric_object (system cZ))
    (f : orbit_hom (system cZ) (val P) (val Q)) :
  exists g : orbit_hom F (preimage (val P)) (preimage (val Q)),
    orbit_map cZ g == f.
Proof.
have [g hg] := @orbit_map_surjective S F Z cZ (val P) (val Q) f.
by exists g; apply/eqP.
Qed.

Definition lift_orbit (P Q : centric_object (system cZ))
    (f : orbit_hom (system cZ) (val P) (val Q)) :
    orbit_hom F (preimage (val P)) (preimage (val Q)) :=
  xchoose (lift_orbit_exists f).

Lemma orbit_map_lift (P Q : centric_object (system cZ))
    (f : orbit_hom (system cZ) (val P) (val Q)) : orbit_map cZ (lift_orbit f) = f.
Proof. exact: (eqP (xchooseP (lift_orbit_exists f))). Qed.

Lemma lift_orbit_map (P Q : centric_object (system cZ))
    (f : orbit_hom F (preimage (val P)) (preimage (val Q))) :
  @lift_orbit P Q (orbit_map cZ f) = f.
Proof.
apply: (@orbit_map_injective S F Z cZ p pZ sat (val P) (val Q) (valP P)).
exact: orbit_map_lift.
Qed.

Definition lift_functor : functor (centric_orbit_category (system cZ)) preimage_category.
Proof.
refine (@Build_functor (centric_orbit_category (system cZ)) preimage_category
  (fun P => P) (fun P Q f => @lift_orbit P Q f) _ _).
- move=> P.
  apply: (@orbit_map_injective S F Z cZ p pZ sat (val P) (val P) (valP P)).
  by rewrite orbit_map_lift orbit_map_identity.
- move=> P Q R f g.
  apply: (@orbit_map_injective S F Z cZ p pZ sat (val P) (val R) (valP P)).
  by rewrite orbit_map_lift orbit_map_compose !orbit_map_lift.
Defined.

Theorem quotient_lift_identity :
  functor_comp quotient_functor lift_functor = functor_id preimage_category.
Proof.
apply: (@functor_extensionality preimage_category preimage_category
  (functor_comp quotient_functor lift_functor) (functor_id preimage_category) (Logic.eq_refl _)).
apply: functional_extensionality_dep=> P.
apply: functional_extensionality_dep=> Q.
apply: functional_extensionality_dep=> f.
exact: lift_orbit_map.
Qed.

Theorem lift_quotient_identity :
  functor_comp lift_functor quotient_functor =
    functor_id (centric_orbit_category (system cZ)).
Proof.
apply: (@functor_extensionality (centric_orbit_category (system cZ))
  (centric_orbit_category (system cZ)) (functor_comp lift_functor quotient_functor)
  (functor_id (centric_orbit_category (system cZ))) (Logic.eq_refl _)).
apply: functional_extensionality_dep=> P.
apply: functional_extensionality_dep=> Q.
apply: functional_extensionality_dep=> f.
exact: orbit_map_lift.
Qed.

Definition quotient_category_isomorphism :
    category_isomorphism preimage_category (centric_orbit_category (system cZ)) :=
  {| category_iso_forward := quotient_functor;
     category_iso_backward := lift_functor;
     category_iso_forward_backward := quotient_lift_identity;
     category_iso_backward_forward := lift_quotient_identity |}.

End Isomorphism.
End DPFusionQuotientOrbitIso.

Print Assumptions DPFusionQuotientOrbitIso.quotient_category_isomorphism.
