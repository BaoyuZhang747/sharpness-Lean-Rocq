From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryFinite CategoryModules CategoryModuleProducts
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient ModuleNoetherian ModuleNoetherianFinite ModuleFiniteProducts
  HomologicalComplex HomologicalCohomology BarPaths BarComplex BarFinitePaths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkBarPaths DiazParkBarComplex.
Local Open Scope ring_scope.

Section FiniteCohomology.
Variable R : pzRingType.
Hypothesis ring_noetherian : module_noetherian [the lmodType R of R^o].

Theorem finitely_generated_cohomology (C : @cochain_complex R) n :
    module_finitely_generated (cochain_term C n) ->
    module_finitely_generated [the lmodType R of cohomology C n].
Proof.
move=> hC; apply: finitely_generated_quotient.
exact: (finitely_generated_noetherian ring_noetherian hC (cycle_subspace C n)).
Qed.

Variable C : finite_category.
Variable D : module_codiagram R (fc_category C).

Definition finite_bar_product n : lmodType R :=
  module_product_type (fun i : finite_path C n => fobj D (finite_path_start i)).

Definition finite_bar_coordinates n (a : bar_term D n) : finite_bar_product n :=
  fun i => a (finite_path_start i) (finite_path_tail i).

Lemma finite_bar_coordinates_linear n : linear (@finite_bar_coordinates n).
Proof. by move=> r a b; apply functional_extensionality_dep. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (bar_term D n)
  (finite_bar_product n) _
  (@finite_bar_coordinates n) (@finite_bar_coordinates_linear n).

Lemma finite_bar_coordinates_injective n : injective (@finite_bar_coordinates n).
Proof.
move=> a b he; apply functional_extensionality_dep=> x.
apply functional_extensionality_dep=> q.
have [i hi] := finite_path_decode_surjective q.
have h := congr1 (fun z => z (existT _ x i)) he.
change (a x (finite_path_decode i) = b x (finite_path_decode i)) in h.
by rewrite hi in h.
Qed.

Theorem finite_bar_term_finitely_generated n :
    (forall x, module_finitely_generated (fobj D x)) ->
    module_finitely_generated (bar_term D n).
Proof.
move=> hD; apply: noetherian_finitely_generated.
apply: (@module_noetherian_injective R _ _
  (@finite_bar_coordinates n : {linear _ -> _})).
- apply: (@finitely_generated_noetherian R ring_noetherian _).
  apply: finite_product_finitely_generated=> i; exact: hD.
- exact: finite_bar_coordinates_injective.
Qed.

Theorem finite_bar_cohomology_finitely_generated n :
    (forall x, module_finitely_generated (fobj D x)) ->
    module_finitely_generated [the lmodType R of cohomology (bar_complex D) n].
Proof.
move=> hD; apply: finitely_generated_cohomology.
exact: finite_bar_term_finitely_generated hD.
Qed.

End FiniteCohomology.



