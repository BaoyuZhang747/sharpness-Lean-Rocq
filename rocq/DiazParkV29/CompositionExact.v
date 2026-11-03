(** The actual subfunctor/quotient short exact sequence and its complete
    higher-limit long exact sequence.  The connecting map is transported
    through the proved natural bar-to-derived-limit comparison. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness CategoryModuleLinear CategoryDerivedLimits
  CategoryEnoughInjectives CategoryInjectiveResolutionComparison ModuleInfrastructure
  MackeyStructures MackeySubquotients MackeyModuleCarriers MackeyModuleMaps
  MackeyModuleQuotient MackeyBarReduction HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalConnecting HomologicalLongExact HomologicalModuleIso
  BarComplex BarNaturality BarExactness BarDerivedComparison BarScalarHigherLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalConnecting DiazParkBarComplex DiazParkBarNaturality
  DiazParkBarExactness DiazParkBarDerivedComparison DiazParkHomologicalModuleIso
  DiazParkScalarHigherLimits.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution injective_resolution_comparison.

Module DPCompositionExact.

Section ExactTransport.
Variable R : pzRingType.
Variables A B C A' B' C' : lmodType R.
Variables (eA : @isomorphism (module_category R) A A')
  (eB : @isomorphism (module_category R) B B')
  (eC : @isomorphism (module_category R) C C').
Variables (f : {linear A -> B}) (g : {linear B -> C})
  (f' : {linear A' -> B'}) (g' : {linear B' -> C'}).
Hypothesis hf : forall a, f' (module_hom_fun (iso_hom eA) a) =
  module_hom_fun (iso_hom eB) (f a).
Hypothesis hg : forall b, g' (module_hom_fun (iso_hom eB) b) =
  module_hom_fun (iso_hom eC) (g b).

Lemma exact_transport : linear_exact f g -> linear_exact f' g'.
Proof.
move=> h b; split.
- move=> hb.
  have hz : g (module_hom_fun (iso_inv eB) b) = 0.
    apply: (can_inj (module_iso_hom_inv_apply eC)).
    rewrite module_hom_zero -hg module_iso_inv_hom_apply; exact: hb.
  have [a ha] := proj1 (h _) hz.
  exists (module_hom_fun (iso_hom eA) a).
  by rewrite hf ha module_iso_inv_hom_apply.
- move=> [a <-].
  rewrite -(module_iso_inv_hom_apply eA a) hf hg.
  have hz := proj2 (h (f (module_hom_fun (iso_inv eA) a)))
    (ex_intro _ (module_hom_fun (iso_inv eA) a) erefl).
  by rewrite hz module_hom_zero.
Qed.

End ExactTransport.

Section Subquotient.
Variable R : comPzRingType.
Variables C D : category.
Variable B : mackey_shape C.
Variable L : functor D C.
Variable M : mackey_module R B.
Variable N : mackey_subfunctor M.
Let A := mackey_codiagram L (subfunctor_mackey N).
Let B0 := mackey_codiagram L M.
Let Q := mackey_codiagram L (quotient_mackey N).
Let f := mackey_codiagram_map L (subfunctor_inclusion N).
Let g := mackey_codiagram_map L (quotient_projection N).

Definition subquotient_bar_short_exact :
    degreewise_short_exact (bar_cochain_map f) (bar_cochain_map g).
Proof.
apply: bar_short_exact.
- move=> P; exact: submodule_val_injective.
- move=> P x; change (quotient_pi (subfunctor_value N (fobj L P))
    (submodule_val x) = 0).
  apply/quotient_pi_kernel; exact: submodule_val_mem.
- move=> P x; change (quotient_pi (subfunctor_value N (fobj L P)) x = 0 ->
    exists y : submodule_carrier (subfunctor_value N (fobj L P)), submodule_val y = x).
  move/quotient_pi_kernel/submodule_val_range; exact.
- move=> P x; exact: quotient_pi_surjective.
Defined.

Definition subquotient_derived_inclusion n :=
  module_hom_to_linear (derived_limit_map R f n).
Definition subquotient_derived_projection n :=
  module_hom_to_linear (derived_limit_map R g n).
Definition subquotient_derived_connecting n :
    {linear derived_limit R Q n -> derived_limit R A n.+1} :=
  (module_hom_to_linear (iso_hom (bar_derived_limit_iso A n.+1)) \o
    connecting_map subquotient_bar_short_exact n \o
    module_hom_to_linear (iso_inv (bar_derived_limit_iso Q n)) : {linear _ -> _}).

Lemma subquotient_inclusion_comparison n a :
  subquotient_derived_inclusion n
    (module_hom_fun (iso_hom (bar_derived_limit_iso A n)) a) =
  module_hom_fun (iso_hom (bar_derived_limit_iso B0 n))
    (cohomology_map (bar_cochain_map f) n a).
Proof. exact: bar_derived_naturality. Qed.

Lemma subquotient_projection_comparison n a :
  subquotient_derived_projection n
    (module_hom_fun (iso_hom (bar_derived_limit_iso B0 n)) a) =
  module_hom_fun (iso_hom (bar_derived_limit_iso Q n))
    (cohomology_map (bar_cochain_map g) n a).
Proof. exact: bar_derived_naturality. Qed.

Lemma subquotient_connecting_comparison n a :
  subquotient_derived_connecting n
    (module_hom_fun (iso_hom (bar_derived_limit_iso Q n)) a) =
  module_hom_fun (iso_hom (bar_derived_limit_iso A n.+1))
    (connecting_map subquotient_bar_short_exact n a).
Proof. by rewrite /subquotient_derived_connecting /= module_iso_hom_inv_apply. Qed.

Theorem subquotient_higher_limit_long_exact n :
  linear_exact (subquotient_derived_inclusion n) (subquotient_derived_projection n) /\
  linear_exact (subquotient_derived_projection n) (subquotient_derived_connecting n) /\
  linear_exact (subquotient_derived_connecting n) (subquotient_derived_inclusion n.+1).
Proof.
have h := (long_exact_cohomology subquotient_bar_short_exact).2 n.
split.
- exact (@exact_transport R _ _ _ _ _ _
    (bar_derived_limit_iso A n) (bar_derived_limit_iso B0 n) (bar_derived_limit_iso Q n)
    _ _ _ _ (@subquotient_inclusion_comparison n) (@subquotient_projection_comparison n) h.1).
split.
- exact (@exact_transport R _ _ _ _ _ _
    (bar_derived_limit_iso B0 n) (bar_derived_limit_iso Q n) (bar_derived_limit_iso A n.+1)
    _ _ _ _ (@subquotient_projection_comparison n) (@subquotient_connecting_comparison n) h.2.1).
- exact (@exact_transport R _ _ _ _ _ _
    (bar_derived_limit_iso Q n) (bar_derived_limit_iso A n.+1) (bar_derived_limit_iso B0 n.+1)
    _ _ _ _ (@subquotient_connecting_comparison n) (@subquotient_inclusion_comparison n.+1) h.2.2).
Qed.

Theorem subquotient_degree_zero_inclusion_injective :
    injective (subquotient_derived_inclusion 0).
Proof.
move=> x y hxy.
have hco : cohomology_map (bar_cochain_map f) 0
    (module_hom_fun (iso_inv (bar_derived_limit_iso A 0)) x) =
  cohomology_map (bar_cochain_map f) 0
    (module_hom_fun (iso_inv (bar_derived_limit_iso A 0)) y).
  apply: (can_inj (module_iso_hom_inv_apply (bar_derived_limit_iso B0 0))).
  by rewrite -!subquotient_inclusion_comparison !module_iso_inv_hom_apply.
have he := (long_exact_cohomology subquotient_bar_short_exact).1 _ _ hco.
rewrite -(module_iso_inv_hom_apply (bar_derived_limit_iso A 0) x)
  -(module_iso_inv_hom_apply (bar_derived_limit_iso A 0) y).
by rewrite he.
Qed.

Theorem subquotient_derived_extension_zero n
    (hA : forall a : derived_limit R A n, a = 0)
    (hQ : forall q : derived_limit R Q n, q = 0) :
    forall b : derived_limit R B0 n, b = 0.
Proof.
move=> b.
have [a ha] := proj1 ((subquotient_higher_limit_long_exact n).1 b) (hQ _).
rewrite (hA a) linear0 in ha; exact: esym ha.
Qed.

End Subquotient.
End DPCompositionExact.

Print Assumptions DPCompositionExact.subquotient_higher_limit_long_exact.
Print Assumptions DPCompositionExact.subquotient_degree_zero_inclusion_injective.
Print Assumptions DPCompositionExact.subquotient_derived_extension_zero.
