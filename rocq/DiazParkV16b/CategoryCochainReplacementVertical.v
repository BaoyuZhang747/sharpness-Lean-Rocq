(** Native vertical cohomology of the actual category replacement, identified
    with category-bar cochains of the actual cohomology diagram. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleProducts HomologicalComplex HomologicalMaps HomologicalDiagramInjectives
  CategoryFiberVanishing HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient BarPaths BarComplex BarResolutionComparison.
From DiazParkV16b Require Import CochainMapsLaws CochainProductCohomology
  FirstQuadrantCochainTotalMaps CategoryCochainReplacement CategoryCochainCohomologyDiagram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalModuleIso DiazParkBarPaths DiazParkBarComplex
  DiazParkBarResolutionComparison DPCochainMapsLaws DPCochainProduct DPFirstQuadrantTotalMaps.
Local Open Scope ring_scope.

Section Vertical.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).
Variable p : nat.

Definition replacement_column : cochain_complex R := vertical_complex (cochain_replacement_bicomplex K) p.
Definition replacement_path_complex (s : @path C p) := diagram_evaluation_complex K (projT1 s).
Definition replacement_flat_complex := product_complex replacement_path_complex.

Definition replacement_column_projection c (s : @path_from C p c) :
    cochain_map replacement_column (diagram_evaluation_complex K c) :=
  @CochainMap R replacement_column (diagram_evaluation_complex K c)
    (fun q => @bar_evaluation R C (diagram_term K q) p c s)
    (fun q a => Logic.eq_refl).

Definition replacement_flatten_at q (a : cochain_term replacement_column q) :
    cochain_term replacement_flat_complex q :=
  fun s => match s with existT c s => a c s end.

Definition replacement_unflatten_at q (a : cochain_term replacement_flat_complex q) :
    cochain_term replacement_column q := fun c s => a (existT _ c s).

Lemma replacement_flatten_linear q : linear (@replacement_flatten_at q).
Proof. intros r a b; apply functional_extensionality_dep; intros [c s]; reflexivity. Qed.
HB.instance Definition _ q := GRing.isLinear.Build R (cochain_term replacement_column q)
  (cochain_term replacement_flat_complex q) _ (@replacement_flatten_at q) (@replacement_flatten_linear q).
Lemma replacement_unflatten_linear q : linear (@replacement_unflatten_at q).
Proof.
intros r a b; apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s; reflexivity.
Qed.
HB.instance Definition _ q := GRing.isLinear.Build R (cochain_term replacement_flat_complex q)
  (cochain_term replacement_column q) _ (@replacement_unflatten_at q) (@replacement_unflatten_linear q).

Definition replacement_flatten : cochain_map replacement_column replacement_flat_complex.
Proof.
refine (@CochainMap R replacement_column replacement_flat_complex
  (fun q => (@replacement_flatten_at q : {linear _ -> _})) _).
intros q a; apply functional_extensionality_dep; intros [c s]; reflexivity.
Defined.

Definition replacement_unflatten : cochain_map replacement_flat_complex replacement_column.
Proof.
refine (@CochainMap R replacement_flat_complex replacement_column
  (fun q => (@replacement_unflatten_at q : {linear _ -> _})) _).
intros q a; apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s; reflexivity.
Defined.

Definition replacement_flat_cohomology_iso q : @isomorphism (module_category R)
    (cohomology replacement_column q) (cohomology replacement_flat_complex q).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (cohomology_map replacement_flatten q))
  (module_hom_of_linear (cohomology_map replacement_unflatten q)) _ _).
- apply module_hom_ext; intro a.
  change (cohomology_map replacement_unflatten q (cohomology_map replacement_flatten q a) = a).
  have [z <-] := quotient_pi_surjective a.
  rewrite !cohomology_map_pi; congr (quotient_pi _ _).
  apply submodule_val_injective; reflexivity.
- apply module_hom_ext; intro a.
  change (cohomology_map replacement_flatten q (cohomology_map replacement_unflatten q a) = a).
  have [z <-] := quotient_pi_surjective a.
  rewrite !cohomology_map_pi; congr (quotient_pi _ _).
  apply submodule_val_injective; apply functional_extensionality_dep; intros [c s]; reflexivity.
Defined.

Definition replacement_cohomology_uncurry q : module_hom
    (product_cohomology_term replacement_path_complex q)
    (bar_term (cochain_cohomology_diagram K q) p).
Proof.
exists (fun a c s => a (existT _ c s)).
intros r a b; apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s; reflexivity.
Defined.

Definition replacement_cohomology_curry q : module_hom
    (bar_term (cochain_cohomology_diagram K q) p)
    (product_cohomology_term replacement_path_complex q).
Proof.
exists (fun a s => match s with existT c s => a c s end).
intros r a b; apply functional_extensionality_dep; intros [c s]; reflexivity.
Defined.

Definition replacement_cohomology_curry_iso q : @isomorphism (module_category R)
    (product_cohomology_term replacement_path_complex q)
    (bar_term (cochain_cohomology_diagram K q) p).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (replacement_cohomology_uncurry q) (replacement_cohomology_curry q) _ _).
- apply module_hom_ext; intro a; apply functional_extensionality_dep; intros [c s]; reflexivity.
- apply module_hom_ext; intro a; reflexivity.
Defined.

Definition replacement_vertical_cohomology_iso q : @isomorphism (module_category R)
    (cohomology replacement_column q) (bar_term (cochain_cohomology_diagram K q) p) :=
  module_iso_comp (replacement_flat_cohomology_iso q)
    (module_iso_comp (product_cohomology_iso replacement_path_complex q) (replacement_cohomology_curry_iso q)).

Theorem replacement_vertical_cohomology_component q (a : cohomology replacement_column q)
    c (s : @path_from C p c) :
    module_hom_fun (iso_hom (replacement_vertical_cohomology_iso q)) a c s =
      cohomology_map (replacement_column_projection s) q a.
Proof.
change (cohomology_map (product_projection replacement_path_complex (existT _ c s)) q
  (cohomology_map replacement_flatten q a) = cohomology_map (replacement_column_projection s) q a).
symmetry; apply cohomology_composition_of; intro x; reflexivity.
Qed.
End Vertical.
