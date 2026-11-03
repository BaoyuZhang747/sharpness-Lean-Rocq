(** The actual diagram of singular cochains for any topological diagram. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  HomologicalDiagramInjectives CategoryInjectiveResolutionComparison.
From DiazParkV16b Require Import TopologicalCategory SingularSet SingularCohomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularSet DPSingularCohomology DiazParkHomological.

Module DPSingularCochainDiagrams.
Section CochainFunctor.
Variable Real : realType.
Variable R : pzRingType.
Variable A : lmodType R.

Definition singular_cochain_functor (n : nat) :
    functor (opposite topological_category) (module_category R).
Proof.
refine (@Build_functor (opposite topological_category) (module_category R)
  (fun X => cochain_term (singular_cochains Real X A) n)
  (fun X Y f => module_hom_of_linear (cochain_map_at (singular_pullback Real f A) n)) _ _).
- move=> X; apply module_hom_ext => a; apply functional_extensionality_dep => s.
  change (a (compose s (@identity topological_category X)) = a s).
  by rewrite compose_id_right.
- move=> X Y Z f g; apply module_hom_ext => a; apply functional_extensionality_dep => s.
  change (a (continuous_compose s (continuous_compose g f)) =
    a (continuous_compose (continuous_compose s g) f)).
  congr (a _); apply topological_hom_ext => t; reflexivity.
Defined.

Definition singular_cochain_d n :
    nat_trans (singular_cochain_functor n) (singular_cochain_functor n.+1).
Proof.
refine (@Build_nat_trans (opposite topological_category) (module_category R)
  (singular_cochain_functor n) (singular_cochain_functor n.+1)
  (fun X => module_hom_of_linear (cochain_d (singular_cochains Real X A) n)) _).
move=> X Y f; apply module_hom_ext => a; exact: cochain_map_commutes.
Defined.

Definition singular_cochain_diagram (C : category) (X : functor C topological_category) :
    @diagram_complex R (opposite C).
Proof.
refine (@DiagramComplex R (opposite C)
  (fun n => functor_comp (functor_op X) (singular_cochain_functor n))
  (fun n => nat_whisker_left (functor_op X) (singular_cochain_d n)) _).
move=> n c a; exact: cochain_d2.
Defined.

Lemma singular_diagram_at (C : category) (X : functor C topological_category) n c :
  fobj (diagram_term (singular_cochain_diagram X) n) c =
    cochain_term (singular_cochains Real (fobj X c) A) n.
Proof. reflexivity. Qed.
End CochainFunctor.
End DPSingularCochainDiagrams.
