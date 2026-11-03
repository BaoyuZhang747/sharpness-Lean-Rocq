(** The literal realization unit passes from finite skeleta to the whole
    simplicial set once the actual geometric finite-stage lifts are supplied.
    The geometric hypotheses are discharged in a separate final application. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainExhaustiveComparison
  FreeModuleEmbeddings FreeModuleSurjections FreeModuleExhaustive
  SimplicialSet SimplicialSubcomplex SimplicialSkeleton SimplicialChains SimplicialChainsMaps
  SingularSet SingularCohomology TopologicalCategory GeometricRealizationCarrier
  GeometricRealizationMaps RealizationUnitChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPRealizationUnitExhaustive.
Import DiazParkFreeModule DPChainComplex DPChainQuasiIsomorphism DPChainExhaustiveComparison
  DPFreeModuleEmbeddings DPFreeModuleSurjections DPFreeModuleExhaustive
  DPSimplicialSet DPSimplicialSubcomplex DPSimplicialSkeleton
  DPSimplicialChains DPSimplicialChainMaps DPSingularSet DPSingularCohomology
  DPTopological DPGeometricRealization DPGeometricRealizationMaps DPRealizationUnitChains.
Section Passage.
Variable Real : realType.
Variable R : pzRingType.
Variable X : simplicial_set.

Definition source_stage_map k := chain_map_of R (skeleton_inclusion X k).
Definition target_stage_map k := singular_chain_map Real R
  (realization_map Real (skeleton_inclusion X k)).

Lemma source_stage_map_injective k n : injective (chain_map_at (source_stage_map k) n).
Proof.
apply: free_map_injective; exact: subcomplex_inclusion_injective.
Qed.

Lemma source_stage_map_surjective k n (hn : (n <= k)%N) (x : term R X n) :
  exists y, chain_map_at (source_stage_map k) n y = x.
Proof.
apply: free_map_surjective => a.
exists (exist _ a (skeleton_contains_degree a hn)); reflexivity.
Qed.

Definition singular_stage_transition n m (h : (n <= m)%N) :=
  singular_map Real (realization_map Real (skeleton_transition X h)).

Lemma singular_stage_transition_commutes n m (h : (n <= m)%N) d s :
  component (singular_map Real (realization_map Real (skeleton_inclusion X m))) d
    (component (singular_stage_transition h) d s) =
  component (singular_map Real (realization_map Real (skeleton_inclusion X n))) d s.
Proof.
apply: topological_hom_ext => t.
change (realization_map Real (skeleton_inclusion X m)
  (realization_map Real (skeleton_transition X h) (s t)) =
  realization_map Real (skeleton_inclusion X n) (s t)).
have e := realization_map_composition Real (skeleton_transition X h) (skeleton_inclusion X m).
rewrite skeleton_transition_inclusion in e.
exact (esym (f_equal (fun f : hom topological_category
  (realization_space Real (skeleton_set X n)) (realization_space Real X) => f (s t)) e)).
Qed.

Lemma target_stage_monotone n m (h : (n <= m)%N) d
  (y : chain_term (singular_chains Real R (realization_space Real X)) d) :
  (exists z, chain_map_at (target_stage_map n) d z = y) ->
  exists z, chain_map_at (target_stage_map m) d z = y.
Proof.
move=> [z <-].
exists (map_at R (singular_stage_transition h) d z).
apply (free_lift_ext
  (g := (chain_map_at (target_stage_map m) d \o
    map_at R (singular_stage_transition h) d : {linear _ -> _}))
  (h := chain_map_at (target_stage_map n) d)).
move=> s.
change (free_map R (component (singular_map Real (realization_map Real (skeleton_inclusion X m))) d)
  (free_map R (component (singular_stage_transition h) d) (free_basis R s)) =
  free_map R (component (singular_map Real (realization_map Real (skeleton_inclusion X n))) d)
    (free_basis R s)).
rewrite !free_map_basis.
congr (free_basis R _); exact: singular_stage_transition_commutes.
Qed.

Variable hgeom_injective : forall k,
  injective (realization_map Real (skeleton_inclusion X k)).
Variable hgeom_cover : forall d (s : simplex (singular_set Real (realization_space Real X)) d),
  exists k (t : simplex (singular_set Real (realization_space Real (skeleton_set X k))) d),
    component (singular_map Real (realization_map Real (skeleton_inclusion X k))) d t = s.

Lemma target_stage_map_injective k n : injective (chain_map_at (target_stage_map k) n).
Proof.
apply: free_map_injective => s t hst.
apply: topological_hom_ext => a.
apply (@hgeom_injective k _ _).
exact (congr1 (fun f : hom topological_category _ _ => f a) hst).
Qed.

Lemma target_stage_map_cover n
  (y : chain_term (singular_chains Real R (realization_space Real X)) n) :
  exists k z, chain_map_at (target_stage_map k) n z = y.
Proof.
apply: (@free_map_exhaustive R
  (simplex (singular_set Real (realization_space Real X)) n)
  (fun k => simplex (singular_set Real (realization_space Real (skeleton_set X k))) n)
  (fun k => component (singular_map Real (realization_map Real (skeleton_inclusion X k))) n)).
- move=> k m h s [t <-].
  exists (component (singular_stage_transition h) n t).
  exact: singular_stage_transition_commutes.
- exact: hgeom_cover.
Qed.

Theorem realization_unit_quasi_iso_of_skeleta
  (hstage : forall k, quasi_isomorphism (realization_unit_chains Real R (skeleton_set X k))) :
  quasi_isomorphism (realization_unit_chains Real R X).
Proof.
apply (@quasi_iso_of_exhaustive_stages R nat _ _ (realization_unit_chains Real R X)
  (fun k => chains R (skeleton_set X k))
  (fun k => singular_chains Real R (realization_space Real (skeleton_set X k)))
  (fun k => realization_unit_chains Real R (skeleton_set X k)) source_stage_map target_stage_map
  source_stage_map_injective target_stage_map_injective).
- move=> k n x; exact: realization_unit_naturality.
- exact: target_stage_map_cover.
- move=> n y x.
  have [k [y' hy]] := target_stage_map_cover y.
  have [ym hym] := @target_stage_monotone k (maxn k n) (leq_maxl k n) n.+1 y (ex_intro _ y' hy).
  have [xm hxm] := @source_stage_map_surjective (maxn k n) n (leq_maxr k n) x.
  by exists (maxn k n),ym,xm.
- exact hstage.
Qed.
End Passage.
End DPRealizationUnitExhaustive.
