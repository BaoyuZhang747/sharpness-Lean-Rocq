(** The actual two scalar maps on positive derived limits, proved directly
    from field sharpness and residue-field descent, before local sharpness. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp rat.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryDerivedLimits MackeyStructures MackeySubquotients MackeyBarReduction
  MackeyPrimeLocalReduction PrimeLocalRing PrimeLocalTorsionDescent
  FusionSystems FusionOrbit FusionSaturation FusionMackeyShape FusionSharpnessTheorem
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  BarComplex BarNaturality BarDerivedComparison BarHigherLimitVanishing
  BarScalarDivisibility BarScalarDerivedDivisibility BarScalarHigherLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPFusionOrbit DPMackeyPrimeLocal
  DiazParkBarHigherLimitVanishing DiazParkBarDerivedComparison
  DiazParkScalarHigherLimits DiazParkCohomology DiazParkCohomologyMaps
  DiazParkBarComplex DiazParkBarNaturality.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPMackeyPrimeLocalScalar.
Section ScalarMaps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation R := [the comPzRingType of (DPPrimeLocal.type p : Type)].
Local Notation shape := (DPFusionMackey.fusion_mackey_shape F).
Local Notation L := (centric_inclusion F).
Variable M : mackey_module R shape.
Let K := subfunctor_mackey (mackey_scalar_kernel M p%:R).
Let I := subfunctor_mackey (mackey_scalar_image M p%:R).
Let Q := quotient_mackey (mackey_scalar_image M p%:R).
Let a := mackey_codiagram_map L (mackey_scalar_to_image M p%:R).
Let b := mackey_codiagram_map L (subfunctor_inclusion (mackey_scalar_image M p%:R)).

Lemma prime_torsion_bar_acyclic (N : mackey_module R shape)
    (killed : forall P (x : mackey_value N P), p%:R *: x = 0) :
    mackey_bar_acyclic L N.
Proof.
apply: (@DPPrimeLocalTorsion.torsion_acyclic_of_prime_field p hp
  (orbit_category F) shape N killed (centric_orbit_category F) L).
move=> T; apply/(bar_acyclic_chosen_limits_iff (mackey_codiagram L T)).
exact (@DPDiazPark.diaz_park_theorem S F p pS sat [the fieldType of 'F_p] (pchar_Fp hp) T).
Qed.

Lemma scalar_kernel_bar_acyclic : mackey_bar_acyclic L K.
Proof.
apply: prime_torsion_bar_acyclic => P x.
exact (@mackey_scalar_kernel_killed R (orbit_category F) shape M p%:R P x).
Qed.

Lemma scalar_quotient_bar_acyclic : mackey_bar_acyclic L Q.
Proof.
apply: prime_torsion_bar_acyclic => P x.
exact (@mackey_scalar_quotient_killed R (orbit_category F) shape M p%:R P x).
Qed.

Definition scalar_image_higher_iso n : @isomorphism (module_category R)
    (derived_limit R (mackey_codiagram L M) n.+1)
    (derived_limit R (mackey_codiagram L I) n.+1) :=
  @scalar_image_higher_limit_iso R (orbit_category F)
    (centric_orbit_category F) shape L M p%:R scalar_kernel_bar_acyclic n.

Lemma scalar_image_higher_iso_hom n :
    iso_hom (scalar_image_higher_iso n) = derived_limit_map R a n.+1.
Proof. apply module_hom_ext => q; exact: scalar_image_higher_limit_iso_hom. Qed.

Theorem scalar_image_higher_map_invertible n : exists inv : module_hom
    (derived_limit R (mackey_codiagram L I) n.+1)
    (derived_limit R (mackey_codiagram L M) n.+1),
    @compose (module_category R) _ _ _ (derived_limit_map R a n.+1) inv = identity _ /\
    @compose (module_category R) _ _ _ inv (derived_limit_map R a n.+1) = identity _.
Proof.
exists (iso_inv (scalar_image_higher_iso n)).
rewrite -(scalar_image_higher_iso_hom n); split.
- exact: iso_hom_inv.
- exact: iso_inv_hom.
Qed.

Theorem scalar_higher_factor n (q : derived_limit R (mackey_codiagram L M) n) :
    module_hom_fun (derived_limit_map R b n)
      (module_hom_fun (derived_limit_map R a n) q) = p%:R *: q.
Proof.
pose e := bar_derived_limit_iso (mackey_codiagram L M) n.
pose y := module_hom_fun (iso_inv e) q.
have hq : module_hom_fun (iso_hom e) y = q := module_iso_inv_hom_apply e q.
rewrite -{1}hq.
rewrite !bar_derived_naturality scalar_cohomology_factor.
by rewrite module_hom_scale hq.
Qed.

Theorem prime_higher_scalar_surjective n :
    forall q : derived_limit R (mackey_codiagram L M) n.+1,
      exists y, p%:R *: y = q.
Proof.
exact (@mackey_scalar_higher_limit_surjective R (orbit_category F)
  (centric_orbit_category F) shape L M p%:R
  scalar_kernel_bar_acyclic scalar_quotient_bar_acyclic n).
Qed.

Theorem scalar_image_inclusion_higher_surjective n :
    forall q : derived_limit R (mackey_codiagram L M) n.+1,
      exists y : derived_limit R (mackey_codiagram L I) n.+1,
        module_hom_fun (derived_limit_map R b n.+1) y = q.
Proof.
move=> q; have [y hy] := prime_higher_scalar_surjective q.
exists (module_hom_fun (derived_limit_map R a n.+1) y).
by rewrite scalar_higher_factor hy.
Qed.

End ScalarMaps.
End DPMackeyPrimeLocalScalar.
