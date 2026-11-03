(** Actual cohomology isomorphisms induced by compatible degreewise module
    isomorphisms, and functoriality for commuting cochain squares. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleExactness HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.

Section CohomologyIsos.
Variable R : pzRingType.
Variables A B : @cochain_complex R.
Variable e : forall n, @isomorphism (module_category R) (cochain_term A n) (cochain_term B n).
Hypothesis he : forall n x, cochain_d B n (module_hom_fun (iso_hom (e n)) x) =
  module_hom_fun (iso_hom (e n.+1)) (cochain_d A n x).

Definition term_iso_cochain_map : cochain_map A B :=
  @CochainMap R A B (fun n => module_hom_to_linear (iso_hom (e n))) he.

Definition term_iso_cochain_inverse : cochain_map B A.
Proof.
refine (@CochainMap R B A (fun n => module_hom_to_linear (iso_inv (e n))) _).
intros n x. apply (@module_iso_hom_injective R _ _ (e n.+1)).
change (module_hom_fun (iso_hom (e n.+1)) (cochain_d A n (module_hom_fun (iso_inv (e n)) x)) =
  module_hom_fun (iso_hom (e n.+1)) (module_hom_fun (iso_inv (e n.+1)) (cochain_d B n x))).
rewrite -he !module_iso_inv_hom_apply. reflexivity.
Defined.

Definition term_iso_cohomology_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology A n] [the lmodType R of cohomology B n].
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (cohomology_map term_iso_cochain_map n))
  (module_hom_of_linear (cohomology_map term_iso_cochain_inverse n)) _ _).
- apply module_hom_ext; intro q; have [z <-] := quotient_pi_surjective q.
  change (cohomology_map term_iso_cochain_inverse n
    (cohomology_map term_iso_cochain_map n (quotient_pi _ z)) = quotient_pi _ z).
  rewrite !cohomology_map_pi; congr (quotient_pi _ _).
  apply submodule_val_injective; exact: module_iso_hom_inv_apply.
- apply module_hom_ext; intro q; have [z <-] := quotient_pi_surjective q.
  change (cohomology_map term_iso_cochain_map n
    (cohomology_map term_iso_cochain_inverse n (quotient_pi _ z)) = quotient_pi _ z).
  rewrite !cohomology_map_pi; congr (quotient_pi _ _).
  apply submodule_val_injective; exact: module_iso_inv_hom_apply.
Defined.
End CohomologyIsos.

Theorem cohomology_map_square {R : pzRingType} {A B C D : @cochain_complex R}
    (f : cochain_map A B) (g : cochain_map C D)
    (a : cochain_map A C) (b : cochain_map B D)
    (h : forall n x, cochain_map_at b n (cochain_map_at f n x) =
      cochain_map_at g n (cochain_map_at a n x)) n (q : cohomology A n) :
    cohomology_map b n (cohomology_map f n q) = cohomology_map g n (cohomology_map a n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: h.
Qed.
