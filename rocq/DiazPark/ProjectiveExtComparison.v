(** Every actual projective resolution of constant R computes the displayed
    Ext modules, in every degree and for arbitrary coefficient modules.
    Ext is defined independently using actual injective resolutions. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHomLimit
  CategoryEnoughProjectivesResolution ProjectiveExtComplex ProjectiveExtIndependence
  ProjectiveExtBar CategoryDiagramExt CategoryDiagramExtLimits
  BarComplex BarDerivedComparison HomologicalComplex HomologicalCohomology
  HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectiveResolutions DPProjectiveExt DPProjectiveExtIndependence
  DPProjectiveExtBar DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DiazParkBarComplex DiazParkBarDerivedComparison.
Local Open Scope ring_scope.
Local Opaque module_quotient.

Module DPProjectiveExtComparison.
Section Computation.
Variables (R : comPzRingType) (C : category).
Variable P : projective_resolution (constant_regular_diagram R (opposite C)).
Variable D : module_codiagram R C.

Definition projective_resolution_ext_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology (projective_hom_complex P D) n]
    (diagram_ext R (constant_regular_diagram R (opposite C)) D n) :=
  module_iso_comp
    (@projective_hom_resolution_iso R (opposite C) (constant_regular_diagram R (opposite C))
      D P (@bar_projective_resolution R C) n)
    (module_iso_comp (bar_projective_cohomology_iso D n)
      (module_iso_comp (bar_derived_limit_iso D n)
        (iso_symm (constant_ext_derived_limit_iso D n)))).

End Computation.
End DPProjectiveExtComparison.
