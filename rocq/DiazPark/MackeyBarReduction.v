From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyStructures MackeySubquotients MackeyModuleCarriers MackeyModuleMaps
  MackeyModuleQuotient MackeyFiniteLength HomologicalComplex
  BarPaths BarComplex BarNaturality BarExactness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkBarPaths DiazParkBarComplex
  DiazParkBarNaturality DiazParkBarExactness.
Local Open Scope ring_scope.

Section MackeyDiagrams.
Variable R : comPzRingType.
Variables C D : category.
Variable B : mackey_shape C.
Variable L : functor D C.

Definition mackey_codiagram (M : mackey_module R B) : module_codiagram R D.
Proof.
refine (@Build_functor (opposite D) (module_category R)
  (fun P => mackey_value M (fobj L P))
  (fun P Q f => module_hom_of_linear (mackey_pull M (fmap L f))) _ _).
- move=> P; apply: module_hom_ext => x.
  change (mackey_pull M (fmap L (identity P)) x = x).
  by rewrite fmap_id mackey_pull_id.
- move=> P Q T f g; apply: module_hom_ext => x.
  change (mackey_pull M (fmap L (@compose D T Q P g f)) x =
    mackey_pull M (fmap L g) (mackey_pull M (fmap L f) x)).
  by rewrite fmap_compose mackey_pull_comp.
Defined.

Definition mackey_codiagram_map (M N : mackey_module R B) (f : mackey_hom M N) :
    nat_trans (mackey_codiagram M) (mackey_codiagram N).
Proof.
refine (@Build_nat_trans (opposite D) (module_category R)
  (mackey_codiagram M) (mackey_codiagram N)
  (fun P => module_hom_of_linear (mackey_component f (fobj L P))) _).
move=> P Q a; apply: module_hom_ext => x.
exact: mackey_hom_pull.
Defined.

Definition mackey_bar_acyclic (M : mackey_module R B) :=
  positive_acyclic (bar_complex (mackey_codiagram M)).

Lemma mackey_bar_zero M :
    (forall P (x : mackey_value M P), x = 0) -> mackey_bar_acyclic M.
Proof.
move=> h n z hz; exists 0; rewrite linear0.
apply functional_extensionality_dep=> P.
apply functional_extensionality_dep=> p; symmetry; exact: h.
Qed.

Lemma mackey_bar_extension M (N : mackey_subfunctor M) :
    mackey_bar_acyclic (subfunctor_mackey N) ->
    mackey_bar_acyclic (quotient_mackey N) -> mackey_bar_acyclic M.
Proof.
move=> hN hQ.
pose f := mackey_codiagram_map (subfunctor_inclusion N).
pose g := mackey_codiagram_map (quotient_projection N).
have fi P : injective (module_hom_fun (component f P)).
  exact: submodule_val_injective.
have fg P x : module_hom_fun (component g P)
    (module_hom_fun (component f P) x) = 0.
  change (quotient_pi (subfunctor_value N (fobj L P)) (submodule_val x) = 0).
  apply/quotient_pi_kernel; exact: submodule_val_mem.
have fk P x : module_hom_fun (component g P) x = 0 ->
    exists y, module_hom_fun (component f P) y = x.
  change (quotient_pi (subfunctor_value N (fobj L P)) x = 0 ->
    exists y : submodule_carrier (subfunctor_value N (fobj L P)), submodule_val y = x).
  move/quotient_pi_kernel/submodule_val_range; exact.
have gs P x : exists y, module_hom_fun (component g P) y = x.
  exact: quotient_pi_surjective.
exact (@positive_acyclic_extension R _ _ _
  (bar_cochain_map f) (bar_cochain_map g)
  (@bar_short_exact R D _ _ _ f g fi fg fk gs) hN hQ).
Qed.

End MackeyDiagrams.

Section SimpleReduction.
Variable K : fieldType.
Variables C D : category.
Variable B : mackey_shape C.
Variable L : functor D C.
Variable I : finType.
Variable object_at : I -> C.
Hypothesis objects_cover : forall P, exists i, object_at i = P.
Hypothesis simple_acyclic : forall M : mackey_module K B,
  mackey_simple M -> mackey_bar_acyclic L M.

Theorem simple_to_finite_mackey_acyclic (M : mackey_module K B)
    (hM : mackey_finite_values M) :
    mackey_bar_acyclic L M.
Proof.
exact (@finite_mackey_induction K C B I object_at objects_cover
  (mackey_bar_acyclic L) (@mackey_bar_zero K C D B L)
  simple_acyclic (@mackey_bar_extension K C D B L) M hM).
Qed.

End SimpleReduction.
