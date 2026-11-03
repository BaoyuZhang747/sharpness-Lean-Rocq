(** The stronger fixed-degree statement, including degree zero, for finite
    atomic deletion. The map is induced by the actual restriction unit. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryFinite CategoryModules CategoryDerivedLimits
  CategoryAtomicDeletionCore CategoryAtomicDeletionAdjunction CategoryAtomicDeletionSequence
  CategoryAtomicDeletionDerived CategoryAtomicDeletionFiltration CategoryAtomicDeletionTheorem
  HomologicalComplex HomologicalCohomology HomologicalModuleIso HomologicalShortExactMaps
  BarComplex BarDerivedComparison BarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DiazParkBarComplex DiazParkBarDerivedComparison DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Section DegreewiseDeletion.
Variable C : finite_category.
Variable rank : fc_object C -> nat.
Hypothesis rank_mono : forall x y, fc_hom C x y -> (rank x <= rank y)%N.
Hypothesis rank_equal_iso : forall x y, fc_hom C x y -> rank x = rank y -> @fc_isomorphic C x y.
Variable R : pzRingType.
Variable H : fc_object C -> Prop.
Hypothesis Hup : forall (x y : fc_category C), hom (fc_category C) x y -> H x -> H y.
Hypothesis atomic_vanishing : forall q, ~ H q -> forall D : module_codiagram R (fc_category C),
  coefficient_atomic D q -> derived_all_zero D.
Variable D : module_codiagram R (fc_category C).
Local Notation E := (fobj (@full_restriction R (fc_category C) H) D).

Lemma deletion_kernel_all_cohomology_zero n :
  forall q : cohomology (bar_complex (deletion_kernel Hup D)) n, q = 0.
Proof.
have hK : derived_all_zero (deletion_kernel Hup D).
  apply: (@finite_supported_derived_zero C rank rank_mono rank_equal_iso R H atomic_vanishing).
  move=> x hx; exact: deletion_kernel_inside hx.
have ha := proj2 (bar_derived_all_zero_iff _) hK.
exact (proj1 (all_degree_acyclic_cohomology _) ha n).
Qed.

Definition finite_collection_derived_iso n : @isomorphism (module_category R)
    (derived_limit R D n) (derived_limit R E n) :=
  module_iso_comp (iso_symm (bar_derived_limit_iso D n))
    (module_iso_comp
      (cohomology_quotient_iso (deletion_bar_short_exact Hup D)
        (@deletion_kernel_all_cohomology_zero n) (@deletion_kernel_all_cohomology_zero n.+1))
      (module_iso_comp (bar_derived_limit_iso (deletion_truncation Hup D) n)
        (@zero_extension_derived_iso R (fc_category C) H Hup E n))).

Theorem finite_collection_degreewise_zero_iff n :
  (forall q : derived_limit R D n, q = 0) <->
  (forall q : derived_limit R E n, q = 0).
Proof. exact: module_iso_zero_iff (finite_collection_derived_iso n). Qed.

End DegreewiseDeletion.
