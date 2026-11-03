(** Restriction on the shared homogeneous Hom complex is literally the same
    underlying functional, and agrees with the actual native group pullback. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHom CategoryComplexIso
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  BarPaths BarFreeModule ProjectiveExtComplex MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback CategoryBarPullbackPaths
  GroupCohomologyHomogeneousPaths GroupCohomologyHomogeneousMaps
  GroupCohomologyHomogeneousComplex GroupCohomologyHomogeneousEquivariance
  GroupCohomologyHomogeneousProjective GroupCohomologyHomogeneousResolution
  GroupCohomologyHomogeneousComparison GroupCohomologyHomogeneousCohomology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPCategoryBarPullback DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkBarPaths DiazParkFreeModule DPProjectiveExt
  DPGroupCohomologyHomogeneousPaths DPGroupCohomologyHomogeneousMaps
  DPGroupCohomologyHomogeneousComplex DPGroupCohomologyHomogeneousEquivariance
  DPGroupCohomologyHomogeneousProjective DPGroupCohomologyHomogeneousResolution
  DPGroupCohomologyHomogeneousComparison DPGroupCohomologyHomogeneousCohomology.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousRestriction.

Definition subgroup_nested_hom (G : finGroupType) (P Q : {group G}) (h : P \subset Q) :
    {morphism [set: [subg P]] >-> [the finGroupType of [subg Q]]}.
Proof.
apply: (Morphism (mfun := fun x : [subg P] => subg Q (val x))).
move=> x y _ _; apply: subgM; exact: (subsetP h _ (subgP _)).
Defined.

Lemma subgroup_nested_hom_val (G : finGroupType) (P Q : {group G})
    (h : P \subset Q) (x : [subg P]) : val (subgroup_nested_hom h x) = val x.
Proof. apply: subgK; exact: (subsetP h _ (subgP x)). Qed.

Section Restriction.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables P Q : {group G}.
Variable h : P \subset Q.
Variable A : lmodType R.
Local Notation PS := [the finGroupType of [subg P]].
Local Notation QS := [the finGroupType of [subg Q]].

Definition ambient_restrict_term n
    (f : cochain_term (@ambient_hom_complex R G Q A) n) :
    cochain_term (@ambient_hom_complex R G P A) n.
Proof.
refine (@Build_nat_trans (opposite (group_category PS)) (module_category R)
  (homogeneous_diagram R P n) (trivial_codiagram R PS A)
  (fun _ => component f tt) _).
move=> x y a; apply module_hom_ext => v.
have hf := congr1 (fun k => module_hom_fun k v)
  (@naturality _ _ _ _ f tt tt (subgroup_nested_hom h a)).
change (module_hom_fun (component f tt)
  (homogeneous_action R n (val (subgroup_nested_hom h a)) v) =
  module_hom_fun (component f tt) v) in hf.
rewrite subgroup_nested_hom_val in hf; exact hf.
Defined.

Lemma ambient_restrict_term_linear n : linear (@ambient_restrict_term n).
Proof.
move=> r f g; apply diagram_hom_ext => x v; reflexivity.
Qed.

HB.instance Definition _ n := GRing.isLinear.Build R
  (cochain_term (@ambient_hom_complex R G Q A) n)
  (cochain_term (@ambient_hom_complex R G P A) n) _
  (@ambient_restrict_term n) (@ambient_restrict_term_linear n).

Definition ambient_restriction :
    cochain_map (@ambient_hom_complex R G Q A) (@ambient_hom_complex R G P A).
Proof.
refine (@CochainMap R (@ambient_hom_complex R G Q A) (@ambient_hom_complex R G P A)
  (fun n => (@ambient_restrict_term n : {linear _ -> _})) _).
move=> n f; apply diagram_hom_ext => x v; reflexivity.
Defined.

Lemma ambient_restriction_component n
    (f : cochain_term (@ambient_hom_complex R G Q A) n) x v :
  module_hom_fun (component (cochain_map_at ambient_restriction n f) x) v =
    module_hom_fun (component f tt) v.
Proof. reflexivity. Qed.

Lemma nested_vertices n (v : power PS n) :
  vertices_map (subgroup_inclusion_hom Q) n
    (vertices_map (subgroup_nested_hom h) n v) =
  vertices_map (subgroup_inclusion_hom P) n v.
Proof.
elim: n v => [|n IH] v; first reflexivity.
case: v => a v.
change ((val (subgroup_nested_hom h a),
    vertices_map (subgroup_inclusion_hom Q) n (vertices_map (subgroup_nested_hom h) n v)) =
  (val a, vertices_map (subgroup_inclusion_hom P) n v)).
by rewrite subgroup_nested_hom_val IH.
Qed.

Lemma nested_normalized_vertices n (p : @path_from (group_category PS) n tt) :
  vertices_map (subgroup_inclusion_hom Q) n.+1
    (@resolution_generator_to_homogeneous QS n tt
      (existT _ tt (1%g, path_map_from (group_functor (subgroup_nested_hom h)) n tt p))) =
  vertices_map (subgroup_inclusion_hom P) n.+1
    (@resolution_generator_to_homogeneous PS n tt (existT _ tt (1%g, p))).
Proof.
have he := @group_homogeneous_generator_natural PS QS (subgroup_nested_hom h) n tt
  (existT _ tt (1%g, p)).
change (@resolution_generator_to_homogeneous QS n tt
    (existT _ tt (subgroup_nested_hom h 1%g,
      path_map_from (group_functor (subgroup_nested_hom h)) n tt p)) =
  vertices_map (subgroup_nested_hom h) n.+1
    (@resolution_generator_to_homogeneous PS n tt (existT _ tt (1%g, p)))) in he.
rewrite morph1 in he.
rewrite he; exact: nested_vertices.
Qed.

Lemma ambient_restriction_native_square n
    (f : cochain_term (@ambient_hom_complex R G Q A) n) :
  cochain_map_at (@ambient_to_native_cochain R G P A) n
      (cochain_map_at ambient_restriction n f) =
    cochain_map_at (pull_cochain A (subgroup_nested_hom h)) n
      (cochain_map_at (@ambient_to_native_cochain R G Q A) n f).
Proof.
apply functional_extensionality_dep => x; case: x.
apply functional_extensionality_dep => p.
rewrite pull_cochain_at !ambient_to_native_cochain_at.
change (module_hom_fun (component f tt)
    (free_basis R (vertices_map (subgroup_inclusion_hom P) n.+1
      (@resolution_generator_to_homogeneous PS n tt (existT _ tt (1%g, p))))) =
  module_hom_fun (component f tt)
    (free_basis R (vertices_map (subgroup_inclusion_hom Q) n.+1
      (@resolution_generator_to_homogeneous QS n tt
        (existT _ tt (1%g,
          path_map_from (group_functor (subgroup_nested_hom h)) n tt p)))))).
by rewrite nested_normalized_vertices.
Qed.

Lemma ambient_restriction_native_cohomology_square n :
  module_hom_comp (module_hom_of_linear (cohomology_map ambient_restriction n))
    (iso_hom (@ambient_native_iso R G P A n)) =
  module_hom_comp (iso_hom (@ambient_native_iso R G Q A n))
    (pull A (subgroup_nested_hom h) n).
Proof.
rewrite !ambient_native_iso_hom.
apply module_hom_ext => q.
change (cohomology_map (@ambient_to_native_cochain R G P A) n
    (cohomology_map ambient_restriction n q) =
  cohomology_map (pull_cochain A (subgroup_nested_hom h)) n
    (cohomology_map (@ambient_to_native_cochain R G Q A) n q)).
exact (@cohomology_map_square R _ _ _ _ ambient_restriction
  (pull_cochain A (subgroup_nested_hom h))
  (@ambient_to_native_cochain R G Q A) (@ambient_to_native_cochain R G P A)
  ambient_restriction_native_square n q).
Qed.

End Restriction.
End DPGroupCohomologyHomogeneousRestriction.

