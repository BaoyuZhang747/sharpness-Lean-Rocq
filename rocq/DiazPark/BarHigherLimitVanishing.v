From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalCohomology
  HomologicalDiagramLimits CategoryInjectiveResolution CategoryEnoughInjectives
  BarComplex BarInjectiveComparisonAll.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkBarComplex
  DiazParkBarInjectiveComparisonAll.
Local Open Scope ring_scope.

Module DiazParkBarHigherLimitVanishing.
Lemma module_iso_zero_iff {R : pzRingType} {U V : lmodType R}
    (e : @isomorphism (module_category R) U V) :
  (forall x : U, x = 0) <-> (forall y : V, y = 0).
Proof.
split.
- move=> h y; rewrite -(module_iso_inv_hom_apply e y) (h (module_hom_fun (iso_inv e) y)).
  exact: module_hom_zero.
- move=> h x; rewrite -(module_iso_hom_inv_apply e x) (h (module_hom_fun (iso_hom e) x)).
  exact: module_hom_zero.
Qed.

Theorem bar_injective_vanishing_iff {R : pzRingType} {C : category}
    (D : module_codiagram R C) (J : injective_resolution D) n :
  (forall q : cohomology (bar_complex D) n, q = 0) <->
  (forall q : cohomology (limit_complex (injective_resolution_complex J)) n, q = 0).
Proof. exact: (module_iso_zero_iff (bar_injective_cohomology_iso J n)). Qed.

Theorem bar_acyclic_injective_limits_iff {R : pzRingType} {C : category}
    (D : module_codiagram R C) (J : injective_resolution D) :
  positive_acyclic (bar_complex D) <->
  forall n (q : cohomology (limit_complex (injective_resolution_complex J)) n.+1), q = 0.
Proof.
rewrite positive_acyclic_cohomology; split => h n.
- apply/(bar_injective_vanishing_iff J n.+1); exact: h.
- apply/(bar_injective_vanishing_iff J n.+1); exact: h.
Qed.

Theorem bar_acyclic_chosen_limits_iff {R : pzRingType} {C : category}
    (D : module_codiagram R C) :
  positive_acyclic (bar_complex D) <->
  forall n (q : cohomology (limit_complex
    (injective_resolution_complex (chosen_injective_resolution R D))) n.+1), q = 0.
Proof. exact: bar_acyclic_injective_limits_iff. Qed.

End DiazParkBarHigherLimitVanishing.
