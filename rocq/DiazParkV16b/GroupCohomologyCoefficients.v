(** Coefficient maps on actual ordinary group cohomology. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  BarPaths BarComplex BarNaturality BarDerivedComparison
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DiazParkBarComplex DiazParkBarPaths
  DiazParkBarNaturality DiazParkBarDerivedComparison.

Module DPGroupCohomologyCoefficients.
Section Coefficients.
Variable R : comPzRingType.
Variable G : finGroupType.

Definition coefficient_trans (A B : lmodType R) (f : module_hom A B) :
    nat_trans (trivial_codiagram R G A) (trivial_codiagram R G B).
Proof.
refine (@Build_nat_trans (opposite (group_category G)) (module_category R)
  (trivial_codiagram R G A) (trivial_codiagram R G B) (fun _ => f) _).
move=> x y a; apply module_hom_ext => z; reflexivity.
Defined.

Definition coefficient_cochain_map (A B : lmodType R) (f : module_hom A B) :
    cochain_map (complex R G A) (complex R G B) :=
  bar_cochain_map (coefficient_trans f).

Lemma coefficient_cochain_map_at (A B : lmodType R) (f : module_hom A B)
    n (a : cochain_term (complex R G A) n) x (p : path_from n x) :
  cochain_map_at (coefficient_cochain_map f) n a x p = f (a x p).
Proof. reflexivity. Qed.

Definition coefficient_map (A B : lmodType R) (f : module_hom A B) n :
    module_hom (value R G A n) (value R G B n) :=
  module_hom_of_linear (cohomology_map (coefficient_cochain_map f) n).

Lemma coefficient_map_identity (A : lmodType R) n :
  coefficient_map (module_hom_id A) n = module_hom_id (value R G A n).
Proof.
apply module_hom_ext => q.
have [z <-] := quotient_pi_surjective q.
change (cohomology_map (coefficient_cochain_map (module_hom_id A)) n
  (quotient_pi _ z) = quotient_pi _ z).
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Lemma coefficient_map_composition (A B C : lmodType R)
    (f : module_hom A B) (g : module_hom B C) n :
  coefficient_map (module_hom_comp f g) n =
    module_hom_comp (coefficient_map f n) (coefficient_map g n).
Proof.
apply module_hom_ext => q.
have [z <-] := quotient_pi_surjective q.
change (cohomology_map (coefficient_cochain_map (module_hom_comp f g)) n
    (quotient_pi _ z) =
  cohomology_map (coefficient_cochain_map g) n
    (cohomology_map (coefficient_cochain_map f) n (quotient_pi _ z))).
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Definition coefficient_functor (n : nat) : functor (module_category R) (module_category R).
Proof.
refine (@Build_functor (module_category R) (module_category R)
  (fun A => value R G A n) (fun A B f => coefficient_map f n) _ _).
- move=> A; exact: coefficient_map_identity.
- move=> A B C f g; exact: coefficient_map_composition.
Defined.

End Coefficients.
End DPGroupCohomologyCoefficients.
