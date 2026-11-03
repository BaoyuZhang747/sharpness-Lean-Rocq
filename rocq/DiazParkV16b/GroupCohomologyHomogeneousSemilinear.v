(** Semi-equivariant vertex maps induce actual cochain pullbacks. Agreement on
    subgroup vertices gives the literal normalized native comparison. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHom CategoryComplexIso
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  BarPaths BarFreeModule MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback CategoryBarPullbackPaths GroupCohomologyHomogeneousPaths
  GroupCohomologyHomogeneousMaps GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousProjective
  GroupCohomologyHomogeneousComparison GroupCohomologyHomogeneousCohomology
  GroupCohomologyTransferHomogeneous.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPCategoryBarPullback DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkBarPaths DiazParkFreeModule DPGroupCohomologyHomogeneousPaths
  DPGroupCohomologyHomogeneousMaps DPGroupCohomologyHomogeneousComplex
  DPGroupCohomologyHomogeneousEquivariance DPGroupCohomologyHomogeneousProjective
  DPGroupCohomologyHomogeneousComparison DPGroupCohomologyHomogeneousCohomology
  DPGroupCohomologyTransferHomogeneous.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousSemilinear.
Section Semilinear.
Variable R : comPzRingType.
Variables G K : finGroupType.
Variable H : {group G}.
Variable J : {group K}.
Local Notation HS := [the finGroupType of [subg H]].
Local Notation JS := [the finGroupType of [subg J]].
Variable e : {morphism [set: HS] >-> JS}.
Variable phi : G -> K.
Hypothesis hphi : forall (h : HS) x, phi (val h * x)%g = (val (e h) * phi x)%g.
Variable A : lmodType R.

Lemma semilinear_vertices n (h : HS) (v : power G n) :
  vertices_map phi n (left_translate n (val h) v) =
    left_translate n (val (e h)) (vertices_map phi n v).
Proof.
elim: n v => [|n IH] v; first reflexivity.
by case: v => a v; rewrite /= hphi IH.
Qed.

Lemma semilinear_action n (h : HS) (v : homogeneous_term R G n) :
  homogeneous_map R phi n (homogeneous_action R n (val h) v) =
    homogeneous_action R n (val (e h)) (homogeneous_map R phi n v).
Proof.
rewrite /homogeneous_map /homogeneous_action -!free_map_composition.
congr (free_map R _ v); apply functional_extensionality_dep => x.
exact: semilinear_vertices.
Qed.

Definition ambient_semilinear_term n
    (f : cochain_term (@ambient_hom_complex R K J A) n) :
    cochain_term (@ambient_hom_complex R G H A) n.
Proof.
refine (@Build_nat_trans (opposite (group_category HS)) (module_category R)
  (homogeneous_diagram R H n) (trivial_codiagram R HS A)
  (fun _ => module_hom_comp (module_hom_of_linear (homogeneous_map R phi n))
    (component f tt)) _).
move=> x y a; apply module_hom_ext => v.
change (module_hom_fun (component f tt)
    (homogeneous_map R phi n (homogeneous_action R n (val a) v)) =
  module_hom_fun (component f tt) (homogeneous_map R phi n v)).
rewrite semilinear_action.
exact (@ambient_functional_invariant R K J A n f (val (e a))
  (subgP (e a)) (homogeneous_map R phi n v)).
Defined.

Lemma ambient_semilinear_term_linear n : linear (@ambient_semilinear_term n).
Proof. move=> r f g; apply diagram_hom_ext => x v; reflexivity. Qed.

HB.instance Definition _ n := GRing.isLinear.Build R
  (cochain_term (@ambient_hom_complex R K J A) n)
  (cochain_term (@ambient_hom_complex R G H A) n) _
  (@ambient_semilinear_term n) (@ambient_semilinear_term_linear n).

Definition ambient_semilinear :
    cochain_map (@ambient_hom_complex R K J A) (@ambient_hom_complex R G H A).
Proof.
refine (@CochainMap R (@ambient_hom_complex R K J A) (@ambient_hom_complex R G H A)
  (fun n => (@ambient_semilinear_term n : {linear _ -> _})) _).
move=> n f; apply diagram_hom_ext => x v.
change (module_hom_fun (component f tt)
    (homogeneous_map R phi n (homogeneous_boundary R G n v)) =
  module_hom_fun (component f tt)
    (homogeneous_boundary R K n (homogeneous_map R phi n.+1 v))).
by rewrite homogeneous_map_boundary.
Defined.

Lemma ambient_semilinear_component n
    (f : cochain_term (@ambient_hom_complex R K J A) n) x v :
  module_hom_fun (component (cochain_map_at ambient_semilinear n f) x) v =
    module_hom_fun (component f tt) (homogeneous_map R phi n v).
Proof. reflexivity. Qed.

Hypothesis hnormalized : forall h : HS, phi (val h) = val (e h).

Lemma semilinear_subgroup_vertices n (v : power HS n) :
  vertices_map phi n (vertices_map (subgroup_inclusion_hom H) n v) =
    vertices_map (subgroup_inclusion_hom J) n (vertices_map e n v).
Proof.
elim: n v => [|n IH] v; first reflexivity.
case: v => a v; change ((phi (val a),
  vertices_map phi n (vertices_map (subgroup_inclusion_hom H) n v)) =
  (val (e a), vertices_map (subgroup_inclusion_hom J) n (vertices_map e n v))).
by rewrite hnormalized IH.
Qed.

Lemma semilinear_normalized_vertices n (p : @path_from (group_category HS) n tt) :
  vertices_map phi n.+1 (vertices_map (subgroup_inclusion_hom H) n.+1
    (@resolution_generator_to_homogeneous HS n tt (existT _ tt (1%g,p)))) =
  vertices_map (subgroup_inclusion_hom J) n.+1
    (@resolution_generator_to_homogeneous JS n tt
      (existT _ tt (1%g,path_map_from (group_functor e) n tt p))).
Proof.
have he := @group_homogeneous_generator_natural HS JS e n tt
  (existT _ tt (1%g,p)).
change (@resolution_generator_to_homogeneous JS n tt
    (existT _ tt (e 1%g,path_map_from (group_functor e) n tt p)) =
  vertices_map e n.+1 (@resolution_generator_to_homogeneous HS n tt
    (existT _ tt (1%g,p)))) in he.
rewrite morph1 in he; rewrite he; exact: semilinear_subgroup_vertices.
Qed.

Lemma ambient_semilinear_native_square n
    (f : cochain_term (@ambient_hom_complex R K J A) n) :
  cochain_map_at (@ambient_to_native_cochain R G H A) n
    (cochain_map_at ambient_semilinear n f) =
  cochain_map_at (pull_cochain A e) n
    (cochain_map_at (@ambient_to_native_cochain R K J A) n f).
Proof.
apply functional_extensionality_dep => x; case: x.
apply functional_extensionality_dep => p.
rewrite pull_cochain_at !ambient_to_native_cochain_at.
change (module_hom_fun (component f tt)
    (homogeneous_map R phi n (free_basis R
      (vertices_map (subgroup_inclusion_hom H) n.+1
        (@resolution_generator_to_homogeneous HS n tt (existT _ tt (1%g,p)))))) =
  module_hom_fun (component f tt) (free_basis R
    (vertices_map (subgroup_inclusion_hom J) n.+1
      (@resolution_generator_to_homogeneous JS n tt
        (existT _ tt (1%g,path_map_from (group_functor e) n tt p)))))).
by rewrite /homogeneous_map free_map_basis semilinear_normalized_vertices.
Qed.

Lemma ambient_semilinear_native_cohomology_square n :
  module_hom_comp (module_hom_of_linear (cohomology_map ambient_semilinear n))
    (iso_hom (@ambient_native_iso R G H A n)) =
  module_hom_comp (iso_hom (@ambient_native_iso R K J A n)) (pull A e n).
Proof.
rewrite !ambient_native_iso_hom; apply module_hom_ext => q.
change (cohomology_map (@ambient_to_native_cochain R G H A) n
    (cohomology_map ambient_semilinear n q) =
  cohomology_map (pull_cochain A e) n
    (cohomology_map (@ambient_to_native_cochain R K J A) n q)).
exact (@cohomology_map_square R _ _ _ _ ambient_semilinear (pull_cochain A e)
  (@ambient_to_native_cochain R K J A) (@ambient_to_native_cochain R G H A)
  ambient_semilinear_native_square n q).
Qed.

End Semilinear.
End DPGroupCohomologyHomogeneousSemilinear.

