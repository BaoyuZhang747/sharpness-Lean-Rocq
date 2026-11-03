(** Finite-category bar cohomology commutes with the constructed pointwise
    directed colimit, in every nonnegative degree and over arbitrary rings. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryFinite
  CategoryModules CategoryModuleLinear CategoryLimits ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalMaps
  HomologicalCohomology HomologicalCohomologyMaps BarPaths BarFinitePaths
  BarComplex BarNaturality.
From DiazParkV29 Require Import FilteredLimitsDirected FilteredLimitsMaps
  FilteredLimitsCohomology FilteredLimitsDiagrams.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DPFilteredMaps DPFilteredCohomology
  DPFilteredDiagrams DiazParkHomological DiazParkHomologicalMaps
  DiazParkCohomology DiazParkCohomologyMaps DiazParkBarPaths
  DiazParkBarComplex DiazParkBarNaturality.
Local Open Scope ring_scope.

Module DPFilteredBar.
Section FiniteBar.
Variable R : pzRingType.
Variable I : directed_poset.
Variable C : finite_category.
Variable F : functor (stage_category I)
  (functor_category (opposite (fc_category C)) (module_category R)).

Definition bar_system : directed_complex R I.
Proof.
refine (@DirectedComplex R I (fun i => bar_complex (fobj F i))
  (fun i j h => bar_cochain_map (fmap F h)) _ _).
- move=> i h n x.
  replace h with (stage_refl i) by apply Prop_irrelevance.
  change (bar_map_at (fmap F (@identity (stage_category I) i)) x = x).
  rewrite fmap_id; reflexivity.
- move=> i j k h g n x.
  change (bar_map_at (fmap F g) (bar_map_at (fmap F h) x) =
    bar_map_at (fmap F (@compose (stage_category I) i j k h g)) x).
  rewrite fmap_compose; reflexivity.
Defined.

Definition bar_leg i := bar_cochain_map (pointwise_leg F i).
Lemma bar_leg_natural i j (h : stage_le i j) n x :
    cochain_map_at (bar_leg j) n (cochain_map_at (dc_map bar_system h) n x) =
      cochain_map_at (bar_leg i) n x.
Proof.
change (bar_map_at (pointwise_leg F j) (bar_map_at (fmap F h) x) =
  bar_map_at (pointwise_leg F i) x).
rewrite -bar_map_composition pointwise_leg_natural; reflexivity.
Qed.

Definition encode_path n c (p : path_from (C := fc_category C) n c) : finite_path_from (C := C) n c :=
  proj1_sig (constructive_indefinite_description (finite_path_decode_surjective p)).
Lemma encode_path_decode n c (p : path_from (C := fc_category C) n c) :
    finite_path_decode (encode_path p) = p.
Proof. exact: (proj2_sig (constructive_indefinite_description (finite_path_decode_surjective p))). Qed.

Theorem bar_colimit_representatives :
    termwise_representatives (X := bar_system) (@bar_leg).
Proof.
move=> n z.
pose V (t : finite_path C n) := pointwise_system F (finite_path_start t).
pose a (t : finite_path C n) : colimit_module (V t) := z (finite_path_start t) (finite_path_tail t).
have [i [v hv]] := finite_colimit_representatives a.
exists i, (fun c p => v (existT _ c (encode_path p))).
apply functional_extensionality_dep=> c; apply functional_extensionality_dep=> p.
have h := hv (existT _ c (encode_path p)).
change (colimit_in (V := pointwise_system F c) (i := i) (v (existT _ c (encode_path p))) =
  z c (finite_path_decode (encode_path p))) in h.
rewrite encode_path_decode in h; exact h.
Qed.

Theorem bar_colimit_eventual_zero :
    termwise_eventual_zero (X := bar_system) (@bar_leg).
Proof.
move=> i n z hz.
pose V (t : finite_path C n) := pointwise_system F (finite_path_start t).
pose a (t : finite_path C n) : dm_value (V t) i := z (finite_path_start t) (finite_path_tail t).
have ha : forall t, colimit_in (V := V t) (a t) = 0.
  move=> t; exact (congr1 (fun v : bar_term (pointwise_colimit F) n =>
    v (finite_path_start t) (finite_path_tail t)) hz).
have [j [h he]] := finite_colimit_eventual_zero ha.
exists j, h; apply functional_extensionality_dep=> c.
apply functional_extensionality_dep=> p.
have e := he (existT _ c (encode_path p)).
change (module_hom_fun (component (fmap F h) c) (z c (finite_path_decode (encode_path p))) = 0) in e.
rewrite encode_path_decode in e; exact e.
Qed.

Definition bar_colimit_iso n : @isomorphism (module_category R)
    (colimit_module (cohomology_system bar_system n))
    [the lmodType R of cohomology (bar_complex (pointwise_colimit F)) n] :=
  @cohomology_colimit_iso R I bar_system (bar_complex (pointwise_colimit F))
    (@bar_leg) (@bar_leg_natural) bar_colimit_representatives bar_colimit_eventual_zero n.

Lemma bar_colimit_iso_in n i (q : cohomology (bar_complex (fobj F i)) n) :
    module_hom_fun (iso_hom (bar_colimit_iso n))
      (colimit_in (V := cohomology_system bar_system n) (i := i) q) =
    cohomology_map (bar_leg i) n q.
Proof. exact: cohomology_comparison_in. Qed.

End FiniteBar.
End DPFilteredBar.
