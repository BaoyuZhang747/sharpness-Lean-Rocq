(** Finite atomic deletion for genuine derived limits. Atomic vanishing is
    the explicit generic input; the fusion application supplies it separately. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryFinite CategoryModules CategoryDerivedLimits
  CategoryAtomicDeletionCore CategoryAtomicDeletionAdjunction CategoryAtomicDeletionSequence
  CategoryAtomicDeletionDerived CategoryAtomicDeletionFiltration
  HomologicalComplex HomologicalCohomology HomologicalAcyclicQuotient
  BarComplex BarDerivedComparison BarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkBarComplex
  DiazParkBarDerivedComparison DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Definition derived_all_zero {R : pzRingType} {C : category} (D : module_diagram R C) : Prop :=
  forall n (q : derived_limit R D n), q = 0.
Definition derived_positive_zero {R : pzRingType} {C : category} (D : module_diagram R C) : Prop :=
  forall n (q : derived_limit R D n.+1), q = 0.

Lemma bar_derived_all_zero_iff {R : pzRingType} {C : category} (D : module_codiagram R C) :
  all_degree_acyclic (bar_complex D) <-> derived_all_zero D.
Proof.
rewrite all_degree_acyclic_cohomology; split=> h n.
- apply/(module_iso_zero_iff (bar_derived_limit_iso D n)); exact: h.
- apply/(module_iso_zero_iff (bar_derived_limit_iso D n)); exact: h.
Qed.

Lemma bar_derived_positive_zero_iff {R : pzRingType} {C : category} (D : module_codiagram R C) :
  positive_acyclic (bar_complex D) <-> derived_positive_zero D.
Proof. exact: bar_acyclic_chosen_limits_iff. Qed.

Section ZeroExtension.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.
Variable E : module_codiagram R (full_subcategory P).

Lemma zero_extension_all_zero_iff : derived_all_zero (zero_extension Pup E) <-> derived_all_zero E.
Proof.
split=> h n.
- exact (proj1 (module_iso_zero_iff (@zero_extension_derived_iso R C P Pup E n)) (h n)).
- exact (proj2 (module_iso_zero_iff (@zero_extension_derived_iso R C P Pup E n)) (h n)).
Qed.

Lemma zero_extension_positive_zero_iff :
  derived_positive_zero (zero_extension Pup E) <-> derived_positive_zero E.
Proof.
split=> h n.
- exact (proj1 (module_iso_zero_iff (@zero_extension_derived_iso R C P Pup E n.+1)) (h n)).
- exact (proj2 (module_iso_zero_iff (@zero_extension_derived_iso R C P Pup E n.+1)) (h n)).
Qed.
End ZeroExtension.

Section FiniteDeletion.
Variable C : finite_category.
Variable rank : fc_object C -> nat.
Hypothesis rank_mono : forall x y, fc_hom C x y -> (rank x <= rank y)%N.
Hypothesis rank_equal_iso : forall x y, fc_hom C x y -> rank x = rank y -> @fc_isomorphic C x y.
Variable R : pzRingType.
Variable H : fc_object C -> Prop.
Hypothesis Hup : forall (x y : fc_category C), hom (fc_category C) x y -> H x -> H y.
Hypothesis atomic_vanishing : forall q, ~ H q -> forall D : module_codiagram R (fc_category C),
  coefficient_atomic D q -> derived_all_zero D.

Theorem finite_supported_derived_zero (D : module_codiagram R (fc_category C)) :
  (forall x, H x -> forall v : fobj D x, v = 0) -> derived_all_zero D.
Proof.
move=> hD; apply/bar_derived_all_zero_iff.
apply: (@finite_atomic_deletion C rank rank_mono rank_equal_iso R H _ D hD).
move=> q hq E hE; apply/bar_derived_all_zero_iff; exact (@atomic_vanishing q hq E hE).
Qed.

Theorem finite_collection_acyclic_iff (D : module_codiagram R (fc_category C)) :
  derived_positive_zero D <-> derived_positive_zero (fobj (@full_restriction R (fc_category C) H) D).
Proof.
have hK : all_degree_acyclic (bar_complex (deletion_kernel Hup D)).
  apply/bar_derived_all_zero_iff; apply finite_supported_derived_zero.
  move=> x hx; exact: deletion_kernel_inside hx.
have hpK : positive_acyclic (bar_complex (deletion_kernel Hup D)) by move=> n; exact: hK n.+1.
have hseq := positive_acyclic_quotient_iff (deletion_bar_short_exact Hup D) hpK.
rewrite -zero_extension_positive_zero_iff -!bar_derived_positive_zero_iff.
exact hseq.
Qed.

Theorem finite_collection_all_zero_iff (D : module_codiagram R (fc_category C)) :
  derived_all_zero D <-> derived_all_zero (fobj (@full_restriction R (fc_category C) H) D).
Proof.
have hK : all_degree_acyclic (bar_complex (deletion_kernel Hup D)).
  apply/bar_derived_all_zero_iff; apply finite_supported_derived_zero.
  move=> x hx; exact: deletion_kernel_inside hx.
have hseq := all_degree_acyclic_quotient_iff (deletion_bar_short_exact Hup D) hK.
rewrite -zero_extension_all_zero_iff -!bar_derived_all_zero_iff.
exact hseq.
Qed.

End FiniteDeletion.
