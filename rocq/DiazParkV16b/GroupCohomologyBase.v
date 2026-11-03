(** Actual ordinary cohomology of a finite group with arbitrary trivial
    coefficients, using the constructed category bar and independent Ext. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules CategoryDiagramHomLimit
  CategoryDiagramExt CategoryDiagramExtLimits CategoryDerivedLimits
  HomologicalComplex HomologicalCohomology HomologicalModuleIso
  BarComplex BarDerivedComparison MackeyModuleCarriers MackeyModuleQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkHomologicalModuleIso DiazParkBarComplex DiazParkBarDerivedComparison.

Module DPGroupCohomology.

(** Composition is left to right, as in the project's category bar. *)
Definition group_category (G : finGroupType) : category.
Proof.
refine (@Build_category unit (fun _ _ => G) (fun _ => 1%g)
  (fun _ _ _ f g => (f * g)%g) _ _ _).
- intros x y f; exact: mul1g.
- intros x y f; exact: mulg1.
- intros w x y z f g h; symmetry; exact: mulgA.
Defined.

Section TrivialCoefficients.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable A : lmodType R.

Definition trivial_codiagram : module_codiagram R (group_category G).
Proof.
refine (@Build_functor (opposite (group_category G)) (module_category R)
  (fun _ => A) (fun _ _ _ => module_hom_id A) _ _).
- intro x; reflexivity.
- intros x y z f g; apply module_hom_ext; intro a; reflexivity.
Defined.

Definition complex : @cochain_complex R := bar_complex trivial_codiagram.

Definition value (n : nat) : lmodType R :=
  [the lmodType R of cohomology complex n].

(** This comparison is to the independently constructed injective-resolution
    derived limit, in every degree including zero. *)
Definition derived_iso (n : nat) : @isomorphism (module_category R)
    (value n) (derived_limit R trivial_codiagram n) :=
  bar_derived_limit_iso trivial_codiagram n.

(** The displayed group-bar cohomology is actual Ext from the trivial
    regular module, not an arbitrary module equipped with a label. *)
Definition ext_iso (n : nat) : @isomorphism (module_category R)
    (value n)
    (diagram_ext R (constant_regular_diagram R (opposite (group_category G)))
      trivial_codiagram n) :=
  module_iso_comp (derived_iso n)
    (iso_symm (constant_ext_derived_limit_iso trivial_codiagram n)).

End TrivialCoefficients.

Arguments trivial_codiagram R G A : clear implicits.
Arguments complex R G A : clear implicits.
Arguments value R G A n : clear implicits.
Arguments derived_iso R G A n : clear implicits.
Arguments ext_iso R G A n : clear implicits.

End DPGroupCohomology.
