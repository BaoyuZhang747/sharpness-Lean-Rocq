(** Genuine positive derived-limit vanishing supplies exactly the horizontal
    cohomology exactness required by the elementary edge theorem. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  HomologicalComplex HomologicalDiagramInjectives HomologicalCohomology
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  CategoryDerivedLimits BarComplex BarDerivedComparison.
From DiazParkV16b Require Import FirstQuadrantCochainEdge CategoryCochainReplacement
  CategoryCochainCohomologyDiagram CategoryCochainReplacementVertical CategoryCochainReplacementHorizontal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkBarComplex
  DiazParkBarDerivedComparison DPFirstQuadrantEdge.
Local Open Scope ring_scope.

Section Acyclic.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).

Definition replacement_positive_limits_vanish : Prop :=
  forall q p (x : derived_limit R (cochain_cohomology_diagram K q) p.+1), x = 0.

Lemma replacement_bar_positive_exact (hK : replacement_positive_limits_vanish) q p
    (x : bar_term (cochain_cohomology_diagram K q) p.+1)
    (hx : cocycle (bar_complex (cochain_cohomology_diagram K q)) p.+1 x) :
    exists y, bar_d (cochain_cohomology_diagram K q) p y = x.
Proof.
apply (proj1 (cohomology_class_zero hx)).
apply (module_iso_hom_injective (e := bar_derived_limit_iso (cochain_cohomology_diagram K q) p.+1)).
rewrite module_hom_zero. exact: hK.
Qed.

Theorem replacement_positive_horizontal_exact (hK : replacement_positive_limits_vanish) :
    positive_horizontal_exact (cochain_replacement_bicomplex K).
Proof.
intros q p x hx.
pose ep := replacement_vertical_cohomology_iso K p q.
pose en := replacement_vertical_cohomology_iso K p.+1 q.
have hc : cocycle (bar_complex (cochain_cohomology_diagram K q)) p.+1
    (module_hom_fun (iso_hom en) x).
  change (bar_d (cochain_cohomology_diagram K q) p.+1 (module_hom_fun (iso_hom en) x) = 0).
  rewrite -replacement_vertical_cohomology_horizontal hx module_hom_zero.
  reflexivity.
have [y hy] := replacement_bar_positive_exact hK hc.
exists (module_hom_fun (iso_inv ep) y).
apply (module_iso_hom_injective (e := en)).
rewrite replacement_vertical_cohomology_horizontal module_iso_inv_hom_apply.
exact hy.
Qed.
End Acyclic.
