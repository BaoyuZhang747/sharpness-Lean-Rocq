(** Relative comparison from two actual open covers and actual complementary homeomorphisms. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology subtype_topology initial_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology SingularChainMapsLaws
  SingularChainComparison SingularRelativePairs SingularChainExcisionSubspaces
  SingularExcisionSequence SingularExcisionSmallMaps SingularExcisionRelative SingularExcisionQuasiIso
  ChainComplex ChainMapImage ChainRelativePairs ChainQuasiIsomorphism ChainQuasiIsomorphismLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSingularChainMapsLaws DPSingularChainComparison
  DPSingularRelativePairs DPSingularChainExcisionSubspaces DPSingularExcisionSequence
  DPSingularExcisionSmallMaps DPSingularExcisionRelative DPSingularExcisionQuasiIso
  DPChainComplex DPChainMapImage DPChainRelativePairs DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws.
Local Open Scope classical_set_scope.
Module DPSingularRelativeCovers.
Section Covers.
Variable Real : realType.
Variable R : pzRingType.
Variables B Y : topologicalType.
Variable q : continuousType B Y.
Variables (N V : set B) (U W : set Y).
Variable hN : forall b, N b -> U (q b).

Definition cover_neighborhood_map_fun (b : subset_space N) : subset_space U :=
  exist _ (q (val b)) (mem_set (@hN (val b) (set_valP b))).
Lemma cover_neighborhood_map_continuous : continuous cover_neighborhood_map_fun.
Proof.
apply: (@continuous_comp_initial _ (subset_space N) Y set_val).
move=> b; apply: (@continuous_comp (subset_space N) B Y set_val q b);
  [exact: initial_continuous | exact: cts_fun].
Qed.
Definition cover_neighborhood_map : continuousType (subset_space N) (subset_space U) :=
  continuous_map cover_neighborhood_map_continuous.
Lemma cover_neighborhood_square b : q (subset_inclusion N b) =
  subset_inclusion U (cover_neighborhood_map b).
Proof. reflexivity. Qed.
Definition cover_relative_map := @singular_relative_map Real R
  (subset_space N) B (subset_space U) Y (subset_inclusion N) (subset_inclusion U)
  cover_neighborhood_map q cover_neighborhood_square.

Variable eV : homeomorphism (subset_space V) (subset_space W).
Variable eI : homeomorphism (subset_space (V `&` N)) (subset_space (W `&` U)).
Variable heV : forall v, val (iso_hom eV v) = q (val v).
Variable heI : forall v, val (iso_hom eI v) = q (val v).

Lemma cover_intersection_square x :
  iso_hom eV (intersection_left_inclusion V N x) =
    intersection_left_inclusion W U (iso_hom eI x).
Proof. apply: val_inj; change (val (iso_hom eV (intersection_left_inclusion V N x)) = val (iso_hom eI x)); by rewrite heV heI. Qed.
Definition cover_intersection_relative_map := @singular_relative_map Real R
  (subset_space (V `&` N)) (subset_space V) (subset_space (W `&` U)) (subset_space W)
  (intersection_left_inclusion V N) (intersection_left_inclusion W U)
  (iso_hom eI) (iso_hom eV) cover_intersection_square.

Lemma cover_intersection_relative_quasi_isomorphism : quasi_isomorphism cover_intersection_relative_map.
Proof.
apply: singular_relative_map_quasi_isomorphism.
- move=> a b h; apply: val_inj; exact: (congr1 val h).
- move=> a b h; apply: val_inj; exact: (congr1 val h).
- exact: singular_homeomorphism_quasi_isomorphism.
- exact: singular_homeomorphism_quasi_isomorphism.
Qed.

Lemma relative_cover_square n x :
  chain_map_at cover_relative_map n (chain_map_at (relative_excision_map Real R V N) n x) =
    chain_map_at (relative_excision_map Real R W U) n
      (chain_map_at cover_intersection_relative_map n x).
Proof.
have [b <-] := @relative_projection_surjective R _ _ (intersection_to_left Real R V N) n x.
rewrite relative_excision_map_projection /cover_relative_map
  (@singular_relative_map_projection Real R _ _ _ _ (subset_inclusion N) (subset_inclusion U)
    cover_neighborhood_map q cover_neighborhood_square)
  /cover_intersection_relative_map
  (@singular_relative_map_projection Real R _ _ _ _ (intersection_left_inclusion V N)
    (intersection_left_inclusion W U) (iso_hom eI) (iso_hom eV) cover_intersection_square)
  relative_excision_map_projection.
congr (chain_map_at (relative_projection (subspace_chain_inclusion Real U R)) n _).
change (chain_map_at (singular_chain_map Real R q) n
    (chain_map_at (singular_chain_map Real R (subset_inclusion V)) n b) =
  chain_map_at (singular_chain_map Real R (subset_inclusion W)) n
    (chain_map_at (singular_chain_map Real R (iso_hom eV)) n b)).
rewrite -!singular_chain_composition.
have e : @compose topological_category _ _ _ (subset_inclusion V) q = @compose topological_category _ _ _ (iso_hom eV) (subset_inclusion W).
  apply/continuousEP => v; symmetry; exact: heV.
by rewrite e.
Qed.

Theorem cover_relative_quasi_isomorphism (hVo : open V) (hNo : open N)
    (hWo : open W) (hUo : open U)
    (hB : forall b, V b \/ N b) (hY : forall y, W y \/ U y) :
    quasi_isomorphism cover_relative_map.
Proof.
apply: (@quasi_isomorphism_cancel_first R _ _ _ (relative_excision_map Real R V N) cover_relative_map).
- exact: relative_excision_quasi_isomorphism.
- apply: (@quasi_isomorphism_ext R _ _
    (chain_composition cover_intersection_relative_map (relative_excision_map Real R W U))
    (chain_composition (relative_excision_map Real R V N) cover_relative_map)).
  + move=> n x; symmetry; exact: relative_cover_square.
  + apply: quasi_isomorphism_composition.
    * exact: cover_intersection_relative_quasi_isomorphism.
    * exact: relative_excision_quasi_isomorphism.
Qed.
End Covers.
End DPSingularRelativeCovers.
