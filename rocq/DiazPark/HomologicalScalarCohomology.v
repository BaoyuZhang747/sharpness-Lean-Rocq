From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalModuleIso HomologicalScalarRestriction
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkScalarRestriction.
Local Open Scope ring_scope.

Module DiazParkScalarCohomology.
Section Scalars.
Variables A B : pzRingType.
Variable f : {rmorphism A -> B}.

Definition restriction_complex (K : @cochain_complex B) : @cochain_complex A.
Proof.
refine (@CochainComplex A (fun n => restricted_module_type f (cochain_term K n))
  (fun n => restricted_linear f (cochain_d K n)) _).
move=> n x; exact: cochain_d2.
Defined.

Definition restriction_cochain_map {K L : @cochain_complex B} (u : cochain_map K L) :
    cochain_map (restriction_complex K) (restriction_complex L).
Proof.
refine (@CochainMap A (restriction_complex K) (restriction_complex L)
  (fun n => restricted_linear f (cochain_map_at u n)) _).
move=> n x; exact (@cochain_map_commutes B K L u n x).
Defined.

Section Cohomology.
Variable K : @cochain_complex B.
Variable n : nat.
Local Notation KA := (restriction_complex K).
Local Notation HA := (cohomology KA n).
Local Notation HB := (restricted_module_type f [the lmodType B of cohomology K n]).
Local Opaque module_quotient linear_preimage linear_kernel linear_image.

Definition scalar_cycle (z : cycle_module KA n) : cycle_module K n :=
  @cycle_of_cocycle B K n (cycle_inclusion KA n z) (submodule_val_mem z).

Definition scalar_cycle_class (z : cycle_module KA n) : HB :=
  quotient_pi (boundaries_in_cycles K n) (scalar_cycle z).

Lemma scalar_cycle_class_linear : linear scalar_cycle_class.
Proof.
move=> a x y.
change (quotient_pi (boundaries_in_cycles K n) (scalar_cycle (a *: x + y)) =
  f a *: quotient_pi (boundaries_in_cycles K n) (scalar_cycle x) +
  quotient_pi (boundaries_in_cycles K n) (scalar_cycle y)).
rewrite -linearP; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

HB.instance Definition _ := GRing.isLinear.Build A (cycle_module KA n) HB _
  scalar_cycle_class scalar_cycle_class_linear.

Lemma scalar_cycle_class_kernel z :
  boundaries_in_cycles KA n z <-> scalar_cycle_class z = 0.
Proof.
rewrite /scalar_cycle_class quotient_pi_kernel.
change (boundary_subspace KA n (cycle_inclusion KA n z) <->
  boundary_subspace K n (cycle_inclusion KA n z)).
rewrite !boundary_subspaceE; by case: n z.
Qed.

Lemma scalar_cycle_class_surjective : forall q : HB, exists z, scalar_cycle_class z = q.
Proof.
move=> q; have [z <-] := quotient_pi_surjective q.
exists (@cycle_of_cocycle A KA n (cycle_inclusion K n z) (submodule_val_mem z)).
rewrite /scalar_cycle_class; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Definition scalar_cohomology_iso : @isomorphism (module_category A)
    [the lmodType A of HA] HB :=
  quotient_linear_iso scalar_cycle_class_kernel scalar_cycle_class_surjective.

Lemma scalar_cohomology_iso_pi (z : cycle_module KA n) :
  module_hom_fun (iso_hom scalar_cohomology_iso) (quotient_pi (boundaries_in_cycles KA n) z) =
  quotient_pi (boundaries_in_cycles K n) (scalar_cycle z).
Proof. exact: quotient_iso_map_pi. Qed.

End Cohomology.

Lemma scalar_cohomology_naturality (K L : @cochain_complex B) (u : cochain_map K L) n
    (q : cohomology (restriction_complex K) n) :
  module_hom_fun (iso_hom (scalar_cohomology_iso L n))
    (cohomology_map (restriction_cochain_map u) n q) =
  restricted_linear f (cohomology_map u n)
    (module_hom_fun (iso_hom (scalar_cohomology_iso K n)) q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi !scalar_cohomology_iso_pi.
change (quotient_pi (boundaries_in_cycles L n)
  (scalar_cycle (cycle_map (restriction_cochain_map u) n z)) =
  cohomology_map u n (quotient_pi (boundaries_in_cycles K n) (scalar_cycle z))).
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

End Scalars.
End DiazParkScalarCohomology.
