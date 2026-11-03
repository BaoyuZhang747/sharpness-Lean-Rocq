From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import Category CategoryReindex FusionMaps FusionSystems
  FusionOrbit FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientNormalization FusionQuotientOrbitMaps.
Import DPFusionOrbit DPFusionQuotientConstruction DPFusionQuotientNormalization
  DPFusionQuotientOrbitMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientOrbitFunctor.
Section QuotientFunctor.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Definition preimage_orbit_category : category :=
  reindexed_category (orbit_category F) (fun P : {group coset_of Z} => preimage P).

Definition preimage_quotient_functor :
    functor preimage_orbit_category (orbit_category (system cZ)).
Proof.
  refine (@Build_functor preimage_orbit_category (orbit_category (system cZ))
    (fun P => P) (fun P Q f => orbit_map cZ f) _ _).
  - intro P; exact: orbit_map_identity.
  - intros P Q R f g; exact: orbit_map_compose.
Defined.

Definition containing_object := {P : {group S} | Z \subset P}.
Definition containing_category : category :=
  reindexed_category (orbit_category F) (fun P : containing_object => val P).
Definition quotient_object (P : containing_object) : {group coset_of Z} := (val P / Z)%G.

(** The quotient functor on every subgroup containing Z. No centricity,
    p-group, or saturation hypothesis is used in its construction. *)
Definition quotient_functor : functor containing_category (orbit_category (system cZ)).
Proof.
  refine (functor_comp
    (@reindex_change (orbit_category F) containing_object
      (fun P => val P) (fun P => preimage (quotient_object P))
      (fun P => esym (preimage_of_quotient cZ (valP P)))) _).
  refine (functor_comp
    (@reindex_unflatten (orbit_category F) {group coset_of Z} containing_object
      (fun P => preimage P) quotient_object) _).
  exact (functor_comp (reindex_inclusion preimage_orbit_category quotient_object)
    preimage_quotient_functor).
Defined.

Theorem quotient_functor_object (P : containing_object) :
  fobj quotient_functor P = (val P / Z)%G.
Proof. reflexivity. Qed.

Theorem quotient_functor_map (P Q : containing_object)
    (f : orbit_hom F (val P) (val Q)) :
  fmap quotient_functor f = orbit_map cZ
    (@hom_transport (orbit_category F) (val P) (val Q)
      (preimage (val P / Z)%G) (preimage (val Q / Z)%G)
      (esym (preimage_of_quotient cZ (valP P)))
      (esym (preimage_of_quotient cZ (valP Q))) f).
Proof. reflexivity. Qed.
End QuotientFunctor.
End DPFusionQuotientOrbitFunctor.

Print Assumptions DPFusionQuotientOrbitFunctor.quotient_functor.
