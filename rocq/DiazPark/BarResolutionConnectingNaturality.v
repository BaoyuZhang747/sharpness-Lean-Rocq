From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits HomologicalCohomology
  HomologicalCohomologyMaps HomologicalConnecting HomologicalDiagramInjectives HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  BarComplex BarNaturality BarInjectiveResolutionTail BarInjectiveTailMaps BarConnectingLimit BarConnectingNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalConnecting
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarInjectiveResolutionTail DiazParkBarInjectiveTailMaps
  DiazParkBarConnectingLimit DiazParkBarConnectingNaturality.

Module DiazParkBarResolutionConnectingNaturality.
Section Naturality.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_codiagram R C.
Variables (J : injective_resolution D) (J' : injective_resolution E).
Variable u : nat_trans D E.
Variable m : injective_resolution_map J J' u.
Let a := resolution_map_complex m.

Lemma resolution_augmentation_square x (v : fobj D x) :
  module_hom_fun (component (injective_resolution_augmentation J') x)
    (module_hom_fun (component u x) v) =
  module_hom_fun (component (diagram_cochain_map_at a 0) x)
    (module_hom_fun (component (injective_resolution_augmentation J) x) v).
Proof.
symmetry; exact: (congr1 (fun t : nat_trans D
  (diagram_term (injective_resolution_complex J') 0) => module_hom_fun (component t x) v)
  (resolution_map_augmentation m)).
Qed.

Lemma resolution_connecting_naturality n (q : cohomology (bar_complex (injective_syzygy J)) n) :
  connecting_map (injective_syzygy_bar_short_exact J') n
    (cohomology_map (bar_cochain_map (syzygy_comparison m)) n q) =
  cohomology_map (bar_cochain_map u) n.+1
    (connecting_map (injective_syzygy_bar_short_exact J) n q).
Proof.
apply: (@bar_connecting_map_naturality R C _ _ _ _ _ _ _ _ _ _
  (injective_syzygy_bar_short_exact J) (injective_syzygy_bar_short_exact J')
  u (diagram_cochain_map_at a 0) (syzygy_comparison m)
  resolution_augmentation_square (syzygy_comparison_square m)).
Qed.

Lemma resolution_limit_connecting_naturality (z : module_limit_type (injective_syzygy J)) :
  limit_connecting (injective_syzygy_bar_short_exact J') (limit_action (syzygy_comparison m) z) =
  cohomology_map (bar_cochain_map u) 1 (limit_connecting (injective_syzygy_bar_short_exact J) z).
Proof.
apply: (@limit_connecting_naturality R C _ _ _ _ _ _ _ _ _ _
  (injective_syzygy_bar_short_exact J) (injective_syzygy_bar_short_exact J')
  u (diagram_cochain_map_at a 0) (syzygy_comparison m)
  resolution_augmentation_square (syzygy_comparison_square m)).
Qed.

End Naturality.
End DiazParkBarResolutionConnectingNaturality.
