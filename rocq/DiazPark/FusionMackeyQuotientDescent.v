From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  FusionMaps FusionSystems FusionOrbit FusionSaturation FusionOuterOrbit
  FusionMackeyShape MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization
  FusionQuotientAutomorphisms FusionQuotientOrbitMaps FusionQuotientOrbitFunctor
  FusionQuotientCollection FusionMackeyQuotientKernelField FusionMackeyQuotientPair
  FusionMackeyQuotientFormula FusionMackeyQuotientCoefficients.
Import DPFusionOrbit DPFusionOuterOrbit DPFusionMackey DPMackeyFusion
  DPFusionQuotientConstruction DPFusionQuotientNormalization DPFusionQuotientAutomorphisms
  DPFusionQuotientOrbitMaps DPFusionMackeyQuotientPair DPFusionMackeyQuotientFormula
  DPFusionMackeyQuotientCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientDescent.
Section SimpleDescent.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable K : fieldType.
Variable M : mackey_pair K (orbit_category F).
Hypothesis hM : inclusion_mackey_formula M.
Let full := full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Variable p : nat.
Hypothesis charp : p \in [pchar K].
Hypothesis pZ : p.-group Z.
Hypothesis sZQ : Z \subset Q.

Lemma descent_kernel_trivial (P : {group coset_of Z}) a
    (aK : a \in 'ker (automorphism_morphism cZ P)) (x : pair_value M (preimage P)) :
  pair_push M (aut_orbit F (preimage P) a) x = x.
Proof.
exact: (@DPFusionMackeyQuotientKernelField.kernel_push_trivial S F Z cZ K M hM
  simple Q leastQ p charp pZ sZQ P a aK x).
Qed.

(** The kernel premise of the generic constructor is discharged above from
    simplicity, characteristic p, and the actual normal p-kernel. *)
Definition simple_quotient_pair := quotient_pair descent_kernel_trivial.

Theorem simple_quotient_inclusion_mackey : inclusion_mackey_formula simple_quotient_pair.
Proof. exact: quotient_inclusion_mackey descent_kernel_trivial hM. Qed.

Definition simple_quotient : mackey_module K (fusion_mackey_shape (system cZ)) :=
  full_mackey_of_inclusions simple_quotient_inclusion_mackey.

Theorem simple_quotient_value (P : {group coset_of Z}) :
  mackey_value simple_quotient P = pair_value M (preimage P).
Proof. reflexivity. Qed.

Theorem simple_quotient_value_quotient (P : {group S}) (hP : Z \subset P) :
  mackey_value simple_quotient (P / Z)%G = pair_value M P.
Proof. change (pair_value M (preimage (P / Z)%G) = pair_value M P).
by rewrite (preimage_of_quotient cZ hP). Qed.

Theorem simple_quotient_push (P T : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage T)) x :
  mackey_push simple_quotient (orbit_map cZ f) x = pair_push M f x.
Proof. exact: quotient_pair_push. Qed.

Theorem simple_quotient_pull (P T : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage T)) x :
  mackey_pull simple_quotient (orbit_map cZ f) x = pair_pull M f x.
Proof. exact: quotient_pair_pull. Qed.

Definition simple_quotient_containing_iso :=
  containing_coefficient_iso descent_kernel_trivial.

Hypothesis sat : DPFusionSaturation.saturated F p.

Definition simple_quotient_collection_iso :=
  collection_coefficient_iso descent_kernel_trivial pZ sat.

End SimpleDescent.
End DPFusionMackeyQuotientDescent.

Print Assumptions DPFusionMackeyQuotientDescent.descent_kernel_trivial.
Print Assumptions DPFusionMackeyQuotientDescent.simple_quotient.
Print Assumptions DPFusionMackeyQuotientDescent.simple_quotient_collection_iso.
